import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT4_H_I_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have h4ehi := hb4.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 4 (by decide) (by decide) with h9 | h9
                · linarith only [h6, h9, hlam]
                · linarith only [h8, h9, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h15 | h15
          · rcases p0_3 (m.d 0 5) (by simp) with h16 | h16
            · rcases m.htr 0 1 2 (by decide) (by decide) with h17 | h17
              · rcases m.htr 0 1 4 (by decide) (by decide) with h18 | h18
                · linarith only [h15, h18, hlam]
                · linarith only [h18, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h17, hlam, p0_0]
            · linarith only [h16, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h15, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · rcases p0_3 (m.d 0 2) (by simp) with h26 | h26
      · rcases p0_3 (m.d 0 3) (by simp) with h27 | h27
        · linarith only [h27, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h29 | h29
          · rcases p0_3 (m.d 0 5) (by simp) with h30 | h30
            · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
              · linarith only [h26, h31, hlam]
              · linarith only [h31, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h30, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h29, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h36 | h36
        · linarith only [h36, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h38 | h38
          · rcases p0_3 (m.d 0 5) (by simp) with h39 | h39
            · rcases m.htr 0 1 2 (by decide) (by decide) with h40 | h40
              · rcases m.htr 0 1 4 (by decide) (by decide) with h41 | h41
                · linarith only [h38, h41, hlam]
                · linarith only [h26, h41, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h26, h40, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h39, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h38, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · linarith only [h25, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h50 | h50
    · linarith only [h50, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h52 | h52
      · rcases p0_3 (m.d 0 3) (by simp) with h53 | h53
        · rcases p0_3 (m.d 0 4) (by simp) with h54 | h54
          · rcases p0_3 (m.d 0 5) (by simp) with h55 | h55
            · rcases m.htr 0 1 2 (by decide) (by decide) with h56 | h56
              · linarith only [h56, hlam, p0_0]
              · linarith only [h56, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h55, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h54, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h61 | h61
          · rcases p0_3 (m.d 0 5) (by simp) with h62 | h62
            · rcases m.htr 0 1 2 (by decide) (by decide) with h63 | h63
              · linarith only [h63, hlam, p0_0]
              · linarith only [h63, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h62, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h61, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h52, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h70 | h70
    · rcases p0_3 (m.d 0 2) (by simp) with h71 | h71
      · rcases p0_3 (m.d 0 3) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 0 5) (by simp) with h75 | h75
            · rcases m.htr 0 1 2 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
                · rcases m.htr 0 1 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h74, h80, hlam]
                      · linarith only [h80, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h79, hlam, p0_0]
                  · linarith only [h76, h78, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h76, h77, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h70, h76, hlam]
            · linarith only [h75, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h74, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h71, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h90 | h90
      · rcases p0_3 (m.d 0 3) (by simp) with h91 | h91
        · linarith only [h91, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h93 | h93
          · rcases p0_3 (m.d 0 5) (by simp) with h94 | h94
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · linarith only [h70, h95, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h70, h95, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h94, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h93, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h90, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h109 | h109
              · linarith only [h109, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h105, h109, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h105, h108, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h105, h107, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h106, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h115 | h115
        · rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 0 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h105, h118, hlam]
            · linarith only [h117, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h116, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h115, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h124 | h124
    · rcases p0_3 (m.d 0 2) (by simp) with h125 | h125
      · linarith only [h125, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h127 | h127
        · rcases p0_3 (m.d 0 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · rcases m.htr 0 1 2 (by decide) (by decide) with h130 | h130
              · rcases m.htr 0 1 4 (by decide) (by decide) with h131 | h131
                · rcases m.htr 0 1 5 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h133 | h133
                    · linarith only [h133, hlam, p0_0]
                    · linarith only [h133, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h124, h130, h132, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h124, h130, h131, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h124, h130, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h124, h129, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h124, h128, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h127, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h142 | h142
      · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h144 | h144
        · rcases p0_3 (m.d 0 4) (by simp) with h145 | h145
          · rcases p0_3 (m.d 0 5) (by simp) with h146 | h146
            · rcases m.htr 0 1 2 (by decide) (by decide) with h147 | h147
              · linarith only [h124, h147, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h149 | h149
                · linarith only [h147, h149, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h145, h147, h149, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h146, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h145, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h144, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h158 | h158
    · linarith only [h158, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h160 | h160
      · rcases p0_3 (m.d 0 3) (by simp) with h161 | h161
        · rcases p0_3 (m.d 0 4) (by simp) with h162 | h162
          · rcases p0_3 (m.d 0 5) (by simp) with h163 | h163
            · rcases m.htr 0 1 2 (by decide) (by decide) with h164 | h164
              · linarith only [h160, h164, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h160, h164, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h160, h163, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h162, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h169 | h169
          · rcases p0_3 (m.d 0 5) (by simp) with h170 | h170
            · rcases m.htr 0 1 2 (by decide) (by decide) with h171 | h171
              · linarith only [h160, h171, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h160, h171, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h160, h170, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h169, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h176 | h176
        · rcases p0_3 (m.d 0 4) (by simp) with h177 | h177
          · rcases p0_3 (m.d 0 5) (by simp) with h178 | h178
            · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
              · linarith only [h179, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h160, h179, hlam]
            · linarith only [h178, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h177, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
          · rcases p0_3 (m.d 0 5) (by simp) with h185 | h185
            · rcases m.htr 0 1 2 (by decide) (by decide) with h186 | h186
              · linarith only [h186, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h160, h186, hlam]
            · linarith only [h185, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h184, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h191 | h191
    · rcases p0_3 (m.d 0 2) (by simp) with h192 | h192
      · linarith only [h192, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h194 | h194
        · rcases p0_3 (m.d 0 4) (by simp) with h195 | h195
          · rcases p0_3 (m.d 0 5) (by simp) with h196 | h196
            · rcases m.htr 0 1 2 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 1 4 (by decide) (by decide) with h198 | h198
                · rcases m.htr 0 1 5 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h200 | h200
                    · linarith only [h198, h200, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h194, h200, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h197, h198, h199, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h191, h198, hlam]
              · linarith only [h191, h197, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h191, h196, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h195, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h208 | h208
          · rcases p0_3 (m.d 0 5) (by simp) with h209 | h209
            · rcases m.htr 0 1 2 (by decide) (by decide) with h210 | h210
              · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
                · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
                    · linarith only [h211, h213, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h194, h213, hlam]
                  · linarith only [h211, h212, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h191, h211, hlam]
              · linarith only [h191, h210, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h191, h209, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h208, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h221 | h221
      · linarith only [h221, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h223 | h223
        · rcases p0_3 (m.d 0 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · linarith only [h191, h226, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
                · linarith only [h226, h228, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h226, h228, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h225, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h224, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h233 | h233
          · rcases p0_3 (m.d 0 5) (by simp) with h234 | h234
            · rcases m.htr 0 1 2 (by decide) (by decide) with h235 | h235
              · linarith only [h191, h235, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h237 | h237
                · linarith only [h235, h237, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h235, h237, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h234, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h233, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h242 | h242
    · rcases p0_3 (m.d 0 2) (by simp) with h243 | h243
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · linarith only [h244, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h246 | h246
          · rcases p0_3 (m.d 0 5) (by simp) with h247 | h247
            · rcases m.htr 0 1 2 (by decide) (by decide) with h248 | h248
              · rcases m.htr 0 1 4 (by decide) (by decide) with h249 | h249
                · rcases m.htr 0 1 5 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h251 | h251
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h252 | h252
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h253 | h253
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h254 | h254
                          · linarith only [h254, hlam, p0_0]
                          · linarith only [h251, h254, hc23, hc34, hlam, hphi, p0_1]
                        · linarith only [h251, h252, h253, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h243, h252, hlam]
                    · linarith only [h243, h251, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h249, h250, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h242, h249, hlam]
              · linarith only [h242, h248, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h242, h247, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h246, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h265 | h265
        · linarith only [h265, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h267 | h267
          · rcases p0_3 (m.d 0 5) (by simp) with h268 | h268
            · rcases m.htr 0 1 2 (by decide) (by decide) with h269 | h269
              · rcases m.htr 0 1 4 (by decide) (by decide) with h270 | h270
                · rcases m.htr 0 1 5 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h272 | h272
                    · linarith only [h243, h272, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h274 | h274
                      · linarith only [h270, h272, h274, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h269, h272, h274, hc12, hc24, hlam, hphi, p0_1]
                  · linarith only [h270, h271, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h242, h270, hlam]
              · linarith only [h242, h243, h269, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h242, h268, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h267, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h282 | h282
      · rcases p0_3 (m.d 0 3) (by simp) with h283 | h283
        · linarith only [h283, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h285 | h285
          · rcases p0_3 (m.d 0 5) (by simp) with h286 | h286
            · rcases m.htr 0 1 2 (by decide) (by decide) with h287 | h287
              · linarith only [h242, h287, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h242, h282, h287, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h282, h286, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h285, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · rcases m.htr 0 1 2 (by decide) (by decide) with h296 | h296
              · linarith only [h242, h296, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h298 | h298
                · linarith only [h282, h296, h298, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h282, h296, h298, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h295, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
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
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h305 | h305
    · linarith only [h305, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h307 | h307
      · rcases p0_3 (m.d 0 3) (by simp) with h308 | h308
        · rcases p0_3 (m.d 0 4) (by simp) with h309 | h309
          · rcases p0_3 (m.d 0 5) (by simp) with h310 | h310
            · rcases m.htr 0 1 2 (by decide) (by decide) with h311 | h311
              · linarith only [h307, h311, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h307, h311, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h310, hlam, p0_0]
          · linarith only [h307, h309, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h316 | h316
          · rcases p0_3 (m.d 0 5) (by simp) with h317 | h317
            · rcases m.htr 0 1 2 (by decide) (by decide) with h318 | h318
              · linarith only [h307, h318, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h307, h318, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h317, hlam, p0_0]
          · linarith only [h307, h316, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h323 | h323
        · rcases p0_3 (m.d 0 4) (by simp) with h324 | h324
          · rcases p0_3 (m.d 0 5) (by simp) with h325 | h325
            · rcases m.htr 0 1 2 (by decide) (by decide) with h326 | h326
              · linarith only [h326, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h307, h326, hlam]
            · linarith only [h325, hlam, p0_0]
          · linarith only [h324, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h331 | h331
          · rcases p0_3 (m.d 0 5) (by simp) with h332 | h332
            · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
              · linarith only [h333, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h307, h333, hlam]
            · linarith only [h332, hlam, p0_0]
          · linarith only [h331, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h338 | h338
    · rcases p0_3 (m.d 0 2) (by simp) with h339 | h339
      · linarith only [h339, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h341 | h341
        · rcases p0_3 (m.d 0 4) (by simp) with h342 | h342
          · rcases p0_3 (m.d 0 5) (by simp) with h343 | h343
            · rcases m.htr 0 1 2 (by decide) (by decide) with h344 | h344
              · rcases m.htr 0 1 4 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 1 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h347 | h347
                    · linarith only [h342, h345, h347, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h341, h347, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h338, h346, hlam]
                · linarith only [h338, h344, h345, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h338, h344, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h343, hlam, p0_0]
          · linarith only [h338, h342, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h355 | h355
          · rcases p0_3 (m.d 0 5) (by simp) with h356 | h356
            · rcases m.htr 0 1 2 (by decide) (by decide) with h357 | h357
              · rcases m.htr 0 1 4 (by decide) (by decide) with h358 | h358
                · rcases m.htr 0 1 5 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h360 | h360
                    · linarith only [h355, h358, h360, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h341, h360, hlam]
                  · linarith only [h338, h359, hlam]
                · linarith only [h338, h357, h358, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h338, h357, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h356, hlam, p0_0]
          · linarith only [h338, h355, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h368 | h368
      · linarith only [h368, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h370 | h370
        · rcases p0_3 (m.d 0 4) (by simp) with h371 | h371
          · rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
            · rcases m.htr 0 1 2 (by decide) (by decide) with h373 | h373
              · linarith only [h338, h373, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h375 | h375
                · linarith only [h373, h375, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h371, h373, h375, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h372, hlam, p0_0]
          · linarith only [h371, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h380 | h380
          · rcases p0_3 (m.d 0 5) (by simp) with h381 | h381
            · rcases m.htr 0 1 2 (by decide) (by decide) with h382 | h382
              · linarith only [h338, h382, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h384 | h384
                · linarith only [h382, h384, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h380, h382, h384, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h381, hlam, p0_0]
          · linarith only [h380, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h389 | h389
    · rcases p0_3 (m.d 0 2) (by simp) with h390 | h390
      · rcases p0_3 (m.d 0 3) (by simp) with h391 | h391
        · linarith only [h391, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h393 | h393
          · rcases p0_3 (m.d 0 5) (by simp) with h394 | h394
            · rcases m.htr 0 1 2 (by decide) (by decide) with h395 | h395
              · rcases m.htr 0 1 4 (by decide) (by decide) with h396 | h396
                · rcases m.htr 0 1 5 (by decide) (by decide) with h397 | h397
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h398 | h398
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h399 | h399
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h400 | h400
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h401 | h401
                          · linarith only [h393, h395, h399, h401, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                          · linarith only [h393, h401, hc03, hc34, hlam, hphi, p0_1]
                        · linarith only [h390, h400, hlam]
                      · linarith only [h390, h398, h399, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h390, h398, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h389, h397, hlam]
                · linarith only [h389, h396, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h389, h395, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h394, hlam, p0_0]
          · linarith only [h389, h393, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h412 | h412
        · linarith only [h412, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h414 | h414
          · rcases p0_3 (m.d 0 5) (by simp) with h415 | h415
            · rcases m.htr 0 1 2 (by decide) (by decide) with h416 | h416
              · rcases m.htr 0 1 4 (by decide) (by decide) with h417 | h417
                · rcases m.htr 0 1 5 (by decide) (by decide) with h418 | h418
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h419 | h419
                    · linarith only [h390, h419, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h421 | h421
                      · linarith only [h414, h417, h419, h421, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h414, h416, h419, h421, hc12, hc24, hlam, hphi, p0_1]
                  · linarith only [h389, h418, hlam]
                · linarith only [h389, h417, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h389, h390, h416, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h415, hlam, p0_0]
          · linarith only [h389, h414, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h429 | h429
      · rcases p0_3 (m.d 0 3) (by simp) with h430 | h430
        · linarith only [h430, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h432 | h432
          · rcases p0_3 (m.d 0 5) (by simp) with h433 | h433
            · rcases m.htr 0 1 2 (by decide) (by decide) with h434 | h434
              · linarith only [h389, h434, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h389, h429, h434, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h433, hlam, p0_0]
          · linarith only [h429, h432, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h439 | h439
        · linarith only [h439, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h441 | h441
          · rcases p0_3 (m.d 0 5) (by simp) with h442 | h442
            · rcases m.htr 0 1 2 (by decide) (by decide) with h443 | h443
              · linarith only [h389, h443, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h445 | h445
                · linarith only [h429, h443, h445, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h429, h441, h443, h445, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h442, hlam, p0_0]
          · linarith only [h441, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.2.1
  have h4ehi := hb4.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h15 | h15
          · rcases p0_3 (m.d 0 5) (by simp) with h16 | h16
            · rcases m.htr 0 1 2 (by decide) (by decide) with h17 | h17
              · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
                · rcases m.htr 0 1 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h16, h19, hlam]
                  · linarith only [h19, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h17, h18, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h17, hlam, p0_0]
            · linarith only [h16, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h15, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h27 | h27
    · rcases p0_3 (m.d 0 2) (by simp) with h28 | h28
      · rcases p0_3 (m.d 0 3) (by simp) with h29 | h29
        · linarith only [h29, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h31 | h31
          · rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · linarith only [h28, h33, hlam]
              · linarith only [h33, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h32, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h31, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h38 | h38
        · linarith only [h38, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h40 | h40
          · rcases p0_3 (m.d 0 5) (by simp) with h41 | h41
            · rcases m.htr 0 1 2 (by decide) (by decide) with h42 | h42
              · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
                · rcases m.htr 0 1 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h41, h44, hlam]
                  · linarith only [h28, h44, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h43, hlam, p0_0]
              · linarith only [h28, h42, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h41, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h40, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · linarith only [h27, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h54 | h54
    · linarith only [h54, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h56 | h56
      · rcases p0_3 (m.d 0 3) (by simp) with h57 | h57
        · rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
          · rcases p0_3 (m.d 0 5) (by simp) with h59 | h59
            · rcases m.htr 0 1 2 (by decide) (by decide) with h60 | h60
              · linarith only [h60, hlam, p0_0]
              · linarith only [h60, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h59, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h58, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h65 | h65
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
              · linarith only [h67, hlam, p0_0]
              · linarith only [h67, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h66, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h65, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h56, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h74 | h74
    · rcases p0_3 (m.d 0 2) (by simp) with h75 | h75
      · rcases p0_3 (m.d 0 3) (by simp) with h76 | h76
        · linarith only [h76, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h78 | h78
          · rcases p0_3 (m.d 0 5) (by simp) with h79 | h79
            · rcases m.htr 0 1 2 (by decide) (by decide) with h80 | h80
              · rcases m.htr 0 1 3 (by decide) (by decide) with h81 | h81
                · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h83 | h83
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h84 | h84
                      · linarith only [h78, h84, hlam]
                      · linarith only [h84, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h83, hlam, p0_0]
                  · linarith only [h80, h81, h82, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h80, h81, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h74, h80, hlam]
            · linarith only [h74, h79, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h74, h78, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h75, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h94 | h94
      · rcases p0_3 (m.d 0 3) (by simp) with h95 | h95
        · linarith only [h95, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h97 | h97
          · rcases p0_3 (m.d 0 5) (by simp) with h98 | h98
            · rcases m.htr 0 1 2 (by decide) (by decide) with h99 | h99
              · linarith only [h74, h99, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h74, h99, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h98, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h97, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h94, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h107 | h107
    · linarith only [h107, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h109 | h109
      · rcases p0_3 (m.d 0 3) (by simp) with h110 | h110
        · rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
          · rcases p0_3 (m.d 0 5) (by simp) with h112 | h112
            · rcases m.htr 0 1 2 (by decide) (by decide) with h113 | h113
              · linarith only [h113, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h109, h113, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h109, h112, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h109, h111, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h110, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h119 | h119
        · rcases p0_3 (m.d 0 4) (by simp) with h120 | h120
          · rcases p0_3 (m.d 0 5) (by simp) with h121 | h121
            · rcases m.htr 0 1 2 (by decide) (by decide) with h122 | h122
              · linarith only [h122, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h109, h122, hlam]
            · linarith only [h121, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h120, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h119, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h128 | h128
    · rcases p0_3 (m.d 0 2) (by simp) with h129 | h129
      · linarith only [h129, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h131 | h131
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · rcases p0_3 (m.d 0 5) (by simp) with h133 | h133
            · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
              · rcases m.htr 0 1 3 (by decide) (by decide) with h135 | h135
                · rcases m.htr 0 1 5 (by decide) (by decide) with h136 | h136
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h137 | h137
                    · linarith only [h137, hlam, p0_0]
                    · linarith only [h137, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h134, h135, h136, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h128, h135, hlam]
              · linarith only [h128, h134, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h128, h133, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h128, h132, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h131, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h146 | h146
      · linarith only [h146, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h148 | h148
        · rcases p0_3 (m.d 0 4) (by simp) with h149 | h149
          · rcases p0_3 (m.d 0 5) (by simp) with h150 | h150
            · rcases m.htr 0 1 2 (by decide) (by decide) with h151 | h151
              · linarith only [h128, h151, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h153 | h153
                · linarith only [h151, h153, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h151, h153, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h150, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h149, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h148, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h162 | h162
    · linarith only [h162, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h164 | h164
      · rcases p0_3 (m.d 0 3) (by simp) with h165 | h165
        · rcases p0_3 (m.d 0 4) (by simp) with h166 | h166
          · rcases p0_3 (m.d 0 5) (by simp) with h167 | h167
            · rcases m.htr 0 1 2 (by decide) (by decide) with h168 | h168
              · linarith only [h164, h168, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h164, h168, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h164, h167, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h173 | h173
          · rcases p0_3 (m.d 0 5) (by simp) with h174 | h174
            · rcases m.htr 0 1 2 (by decide) (by decide) with h175 | h175
              · linarith only [h164, h175, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h164, h175, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h164, h174, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h173, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h180 | h180
        · rcases p0_3 (m.d 0 4) (by simp) with h181 | h181
          · rcases p0_3 (m.d 0 5) (by simp) with h182 | h182
            · rcases m.htr 0 1 2 (by decide) (by decide) with h183 | h183
              · linarith only [h183, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h164, h183, hlam]
            · linarith only [h182, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h181, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h188 | h188
          · rcases p0_3 (m.d 0 5) (by simp) with h189 | h189
            · rcases m.htr 0 1 2 (by decide) (by decide) with h190 | h190
              · linarith only [h190, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h164, h190, hlam]
            · linarith only [h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h188, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h195 | h195
    · rcases p0_3 (m.d 0 2) (by simp) with h196 | h196
      · linarith only [h196, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h198 | h198
        · rcases p0_3 (m.d 0 4) (by simp) with h199 | h199
          · rcases p0_3 (m.d 0 5) (by simp) with h200 | h200
            · rcases m.htr 0 1 2 (by decide) (by decide) with h201 | h201
              · rcases m.htr 0 1 3 (by decide) (by decide) with h202 | h202
                · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h204 | h204
                    · linarith only [h198, h202, h204, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h198, h204, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h198, h201, h202, h203, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h195, h201, h202, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h195, h201, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h195, h200, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h199, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h212 | h212
          · rcases p0_3 (m.d 0 5) (by simp) with h213 | h213
            · rcases m.htr 0 1 2 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 1 3 (by decide) (by decide) with h215 | h215
                · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h217 | h217
                    · linarith only [h213, h216, h217, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h198, h217, hlam]
                  · linarith only [h195, h214, h216, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h195, h214, h215, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h195, h214, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h195, h213, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h212, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h225 | h225
      · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h227 | h227
        · rcases p0_3 (m.d 0 4) (by simp) with h228 | h228
          · rcases p0_3 (m.d 0 5) (by simp) with h229 | h229
            · rcases m.htr 0 1 2 (by decide) (by decide) with h230 | h230
              · linarith only [h195, h230, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h232 | h232
                · linarith only [h230, h232, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h227, h230, h232, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h229, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h228, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h237 | h237
          · rcases p0_3 (m.d 0 5) (by simp) with h238 | h238
            · rcases m.htr 0 1 2 (by decide) (by decide) with h239 | h239
              · linarith only [h195, h239, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h241 | h241
                · linarith only [h239, h241, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h243 | h243
                  · linarith only [h239, h243, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h238, h239, h243, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h238, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h237, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h248 | h248
    · rcases p0_3 (m.d 0 2) (by simp) with h249 | h249
      · rcases p0_3 (m.d 0 3) (by simp) with h250 | h250
        · linarith only [h250, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h252 | h252
          · rcases p0_3 (m.d 0 5) (by simp) with h253 | h253
            · rcases m.htr 0 1 2 (by decide) (by decide) with h254 | h254
              · rcases m.htr 0 1 3 (by decide) (by decide) with h255 | h255
                · rcases m.htr 0 1 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h259 | h259
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
                          · linarith only [h260, hlam, p0_0]
                          · linarith only [h255, h260, hc13, hc34, hlam, hphi, p0_1]
                        · linarith only [h255, h258, h259, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h249, h258, hlam]
                    · linarith only [h249, h255, h257, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h249, h254, h255, h256, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h249, h254, h255, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h248, h254, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h248, h253, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h252, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h271 | h271
        · linarith only [h271, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h273 | h273
          · rcases p0_3 (m.d 0 5) (by simp) with h274 | h274
            · rcases m.htr 0 1 2 (by decide) (by decide) with h275 | h275
              · rcases m.htr 0 1 3 (by decide) (by decide) with h276 | h276
                · rcases m.htr 0 1 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h278 | h278
                    · linarith only [h249, h278, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h280 | h280
                      · linarith only [h274, h277, h278, h280, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h275, h278, h280, hc12, hc24, hlam, hphi, p0_1]
                  · linarith only [h248, h276, h277, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h248, h249, h275, h276, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h248, h249, h275, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h248, h274, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h273, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h288 | h288
      · rcases p0_3 (m.d 0 3) (by simp) with h289 | h289
        · linarith only [h289, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h291 | h291
          · rcases p0_3 (m.d 0 5) (by simp) with h292 | h292
            · rcases m.htr 0 1 2 (by decide) (by decide) with h293 | h293
              · linarith only [h248, h293, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h248, h288, h293, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h288, h292, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h291, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h298 | h298
        · linarith only [h298, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h300 | h300
          · rcases p0_3 (m.d 0 5) (by simp) with h301 | h301
            · rcases m.htr 0 1 2 (by decide) (by decide) with h302 | h302
              · linarith only [h248, h302, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h304 | h304
                · linarith only [h248, h304, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h306 | h306
                  · linarith only [h288, h302, h306, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h288, h301, h302, h306, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h301, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h300, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h313 | h313
    · linarith only [h313, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h315 | h315
      · rcases p0_3 (m.d 0 3) (by simp) with h316 | h316
        · rcases p0_3 (m.d 0 4) (by simp) with h317 | h317
          · rcases p0_3 (m.d 0 5) (by simp) with h318 | h318
            · rcases m.htr 0 1 2 (by decide) (by decide) with h319 | h319
              · linarith only [h315, h319, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h315, h319, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h318, hlam, p0_0]
          · linarith only [h315, h317, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h324 | h324
          · rcases p0_3 (m.d 0 5) (by simp) with h325 | h325
            · rcases m.htr 0 1 2 (by decide) (by decide) with h326 | h326
              · linarith only [h315, h326, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h315, h326, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h325, hlam, p0_0]
          · linarith only [h315, h324, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h331 | h331
        · rcases p0_3 (m.d 0 4) (by simp) with h332 | h332
          · rcases p0_3 (m.d 0 5) (by simp) with h333 | h333
            · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
              · linarith only [h334, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h315, h334, hlam]
            · linarith only [h333, hlam, p0_0]
          · linarith only [h332, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h339 | h339
          · rcases p0_3 (m.d 0 5) (by simp) with h340 | h340
            · rcases m.htr 0 1 2 (by decide) (by decide) with h341 | h341
              · linarith only [h341, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h315, h341, hlam]
            · linarith only [h340, hlam, p0_0]
          · linarith only [h339, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h346 | h346
    · rcases p0_3 (m.d 0 2) (by simp) with h347 | h347
      · linarith only [h347, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h349 | h349
        · rcases p0_3 (m.d 0 4) (by simp) with h350 | h350
          · rcases p0_3 (m.d 0 5) (by simp) with h351 | h351
            · rcases m.htr 0 1 2 (by decide) (by decide) with h352 | h352
              · rcases m.htr 0 1 3 (by decide) (by decide) with h353 | h353
                · rcases m.htr 0 1 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h355 | h355
                    · linarith only [h349, h353, h355, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h349, h355, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h346, h354, hlam]
                · linarith only [h346, h352, h353, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h346, h352, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h351, hlam, p0_0]
          · linarith only [h346, h350, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h363 | h363
          · rcases p0_3 (m.d 0 5) (by simp) with h364 | h364
            · rcases m.htr 0 1 2 (by decide) (by decide) with h365 | h365
              · rcases m.htr 0 1 3 (by decide) (by decide) with h366 | h366
                · rcases m.htr 0 1 5 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h368 | h368
                    · linarith only [h367, h368, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h349, h368, hlam]
                  · linarith only [h346, h367, hlam]
                · linarith only [h346, h365, h366, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h346, h365, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h364, hlam, p0_0]
          · linarith only [h346, h363, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h376 | h376
      · linarith only [h376, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h378 | h378
        · rcases p0_3 (m.d 0 4) (by simp) with h379 | h379
          · rcases p0_3 (m.d 0 5) (by simp) with h380 | h380
            · rcases m.htr 0 1 2 (by decide) (by decide) with h381 | h381
              · linarith only [h346, h381, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h383 | h383
                · linarith only [h381, h383, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h378, h381, h383, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h380, hlam, p0_0]
          · linarith only [h379, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h388 | h388
          · rcases p0_3 (m.d 0 5) (by simp) with h389 | h389
            · rcases m.htr 0 1 2 (by decide) (by decide) with h390 | h390
              · linarith only [h346, h390, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h392 | h392
                · linarith only [h390, h392, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h394 | h394
                  · linarith only [h390, h394, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h390, h394, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h389, hlam, p0_0]
          · linarith only [h388, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h399 | h399
    · rcases p0_3 (m.d 0 2) (by simp) with h400 | h400
      · rcases p0_3 (m.d 0 3) (by simp) with h401 | h401
        · linarith only [h401, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h403 | h403
          · rcases p0_3 (m.d 0 5) (by simp) with h404 | h404
            · rcases m.htr 0 1 2 (by decide) (by decide) with h405 | h405
              · rcases m.htr 0 1 3 (by decide) (by decide) with h406 | h406
                · rcases m.htr 0 1 5 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h410 | h410
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h411 | h411
                          · linarith only [h403, h405, h409, h411, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                          · linarith only [h403, h411, hc03, hc34, hlam, hphi, p0_1]
                        · linarith only [h400, h410, hlam]
                      · linarith only [h400, h406, h409, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h400, h406, h408, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h399, h407, hlam]
                · linarith only [h399, h406, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h399, h405, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h404, hlam, p0_0]
          · linarith only [h399, h403, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h422 | h422
        · linarith only [h422, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h424 | h424
          · rcases p0_3 (m.d 0 5) (by simp) with h425 | h425
            · rcases m.htr 0 1 2 (by decide) (by decide) with h426 | h426
              · rcases m.htr 0 1 3 (by decide) (by decide) with h427 | h427
                · rcases m.htr 0 1 5 (by decide) (by decide) with h428 | h428
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h429 | h429
                    · linarith only [h400, h429, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h431 | h431
                      · linarith only [h428, h429, h431, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h424, h426, h429, h431, hc12, hc24, hlam, hphi, p0_1]
                  · linarith only [h399, h428, hlam]
                · linarith only [h399, h427, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h399, h400, h426, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h425, hlam, p0_0]
          · linarith only [h399, h424, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h439 | h439
      · rcases p0_3 (m.d 0 3) (by simp) with h440 | h440
        · linarith only [h440, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h442 | h442
          · rcases p0_3 (m.d 0 5) (by simp) with h443 | h443
            · rcases m.htr 0 1 2 (by decide) (by decide) with h444 | h444
              · linarith only [h399, h444, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h399, h439, h444, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h443, hlam, p0_0]
          · linarith only [h439, h442, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h449 | h449
        · linarith only [h449, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h451 | h451
          · rcases p0_3 (m.d 0 5) (by simp) with h452 | h452
            · rcases m.htr 0 1 2 (by decide) (by decide) with h453 | h453
              · linarith only [h399, h453, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h455 | h455
                · linarith only [h399, h455, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h457 | h457
                  · linarith only [h439, h453, h457, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h439, h453, h457, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h452, hlam, p0_0]
          · linarith only [h451, hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_H_I_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
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
          · linarith only [h6, hc02, hlam, hphi, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
            · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h8, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h11 | h11
          · linarith only [h11, hc02, hlam, hphi, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h13 | h13
            · linarith only [h13, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h13, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h17 | h17
    · rcases p0_3 (m.d 0 2) (by simp) with h18 | h18
      · rcases p0_3 (m.d 0 3) (by simp) with h19 | h19
        · linarith only [h19, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · linarith only [h21, hc03, hlam, hphi, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
            · linarith only [h23, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h23, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h28 | h28
          · linarith only [h18, h28, hc02, hlam, hphi, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h30 | h30
            · linarith only [h18, h30, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h30, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h17, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · rcases p0_3 (m.d 0 2) (by simp) with h35 | h35
      · rcases p0_3 (m.d 0 3) (by simp) with h36 | h36
        · rcases p0_3 (m.d 0 4) (by simp) with h37 | h37
          · linarith only [h37, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h39 | h39
            · linarith only [h39, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h39, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
          · linarith only [h42, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h44 | h44
            · linarith only [h36, h44, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h44, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h47 | h47
        · rcases p0_3 (m.d 0 4) (by simp) with h48 | h48
          · linarith only [h48, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h50 | h50
            · linarith only [h35, h50, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h50, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h53 | h53
          · linarith only [h53, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h55 | h55
            · linarith only [h47, h55, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h55, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
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
    rcases p0_3 (m.d 0 1) (by simp) with h60 | h60
    · linarith only [h60, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h62 | h62
      · rcases p0_3 (m.d 0 3) (by simp) with h63 | h63
        · rcases p0_3 (m.d 0 4) (by simp) with h64 | h64
          · linarith only [h64, hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · linarith only [h66, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h66, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h69 | h69
          · linarith only [h69, hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h71 | h71
            · linarith only [h71, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h71, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h62, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h76 | h76
    · rcases p0_3 (m.d 0 2) (by simp) with h77 | h77
      · rcases p0_3 (m.d 0 3) (by simp) with h78 | h78
        · linarith only [h78, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h80 | h80
          · linarith only [h80, hc03, hlam, hphi, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h82 | h82
            · linarith only [h82, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h76, h82, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h77, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h86 | h86
      · rcases p0_3 (m.d 0 3) (by simp) with h87 | h87
        · linarith only [h87, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h89 | h89
          · linarith only [h76, h89, hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h91 | h91
            · linarith only [h76, h91, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h91, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h86, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h95 | h95
    · rcases p0_3 (m.d 0 2) (by simp) with h96 | h96
      · rcases p0_3 (m.d 0 3) (by simp) with h97 | h97
        · rcases p0_3 (m.d 0 4) (by simp) with h98 | h98
          · linarith only [h98, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h100 | h100
            · linarith only [h100, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h100, h95, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · linarith only [h103, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h105 | h105
            · linarith only [h105, h97, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h105, h95, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h96, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h109 | h109
      · rcases p0_3 (m.d 0 3) (by simp) with h110 | h110
        · rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
          · linarith only [h111, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h113 | h113
            · linarith only [h113, h95, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h113, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
          · linarith only [h116, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h118 | h118
            · linarith only [h110, h118, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h118, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h109, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h123 | h123
    · linarith only [h123, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h125 | h125
      · rcases p0_3 (m.d 0 3) (by simp) with h126 | h126
        · rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
          · linarith only [h127, hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · linarith only [h129, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h129, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h126, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h133 | h133
        · rcases p0_3 (m.d 0 4) (by simp) with h134 | h134
          · linarith only [h134, hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h136 | h136
            · linarith only [h136, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h136, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h133, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h140 | h140
    · rcases p0_3 (m.d 0 2) (by simp) with h141 | h141
      · linarith only [h141, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h143 | h143
        · rcases p0_3 (m.d 0 4) (by simp) with h144 | h144
          · linarith only [h144, hc02, hlam, hphi, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h146 | h146
            · linarith only [h146, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h140, h146, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h143, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h150 | h150
      · linarith only [h150, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h152 | h152
        · rcases p0_3 (m.d 0 4) (by simp) with h153 | h153
          · linarith only [h140, h153, hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo0]
          · rcases p0_3 (m.d 0 5) (by simp) with h155 | h155
            · linarith only [h140, h155, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h155, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h152, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 0 2) (by simp) with h161 | h161
      · rcases p0_3 (m.d 0 3) (by simp) with h162 | h162
        · rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
          · linarith only [h163, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
            · linarith only [h165, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h160, h165, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h162, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h169 | h169
        · rcases p0_3 (m.d 0 4) (by simp) with h170 | h170
          · linarith only [h170, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · linarith only [h161, h172, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h172, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h169, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h176 | h176
      · rcases p0_3 (m.d 0 3) (by simp) with h177 | h177
        · rcases p0_3 (m.d 0 4) (by simp) with h178 | h178
          · linarith only [h178, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h180 | h180
            · linarith only [h160, h180, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h176, h180, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h177, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h184 | h184
        · rcases p0_3 (m.d 0 4) (by simp) with h185 | h185
          · linarith only [h185, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h187 | h187
            · linarith only [h176, h187, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h187, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h184, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi5]
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

theorem n7l_sBT4_H_I_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_I_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
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
          · linarith only [h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h11 | h11
          · rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
            · linarith only [h12, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h11, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h17 | h17
    · rcases p0_3 (m.d 0 2) (by simp) with h18 | h18
      · rcases p0_3 (m.d 0 3) (by simp) with h19 | h19
        · linarith only [h19, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · linarith only [h22, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h22, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h21, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · linarith only [h18, h29, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h29, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h28, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
    · linarith only [h17, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 0 3) (by simp) with h39 | h39
        · rcases p0_3 (m.d 0 4) (by simp) with h40 | h40
          · rcases p0_3 (m.d 0 5) (by simp) with h41 | h41
            · linarith only [h41, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h41, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h40, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
          · rcases p0_3 (m.d 0 5) (by simp) with h46 | h46
            · linarith only [h46, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h46, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h45, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h38, hlam, p0_0]
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
          · linarith only [h52, h56, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h62 | h62
      · rcases p0_3 (m.d 0 3) (by simp) with h63 | h63
        · linarith only [h63, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h65 | h65
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · linarith only [h52, h66, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h66, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h65, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h62, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h73 | h73
    · linarith only [h73, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h75 | h75
      · rcases p0_3 (m.d 0 3) (by simp) with h76 | h76
        · rcases p0_3 (m.d 0 4) (by simp) with h77 | h77
          · rcases p0_3 (m.d 0 5) (by simp) with h78 | h78
            · linarith only [h78, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h78, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h77, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h76, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h83 | h83
        · rcases p0_3 (m.d 0 4) (by simp) with h84 | h84
          · rcases p0_3 (m.d 0 5) (by simp) with h85 | h85
            · linarith only [h85, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h85, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h84, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h83, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h90 | h90
    · rcases p0_3 (m.d 0 2) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h93 | h93
        · rcases p0_3 (m.d 0 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 0 5) (by simp) with h95 | h95
            · linarith only [h95, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h90, h95, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h90, h94, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h100 | h100
      · linarith only [h100, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h102 | h102
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · linarith only [h104, h90, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h104, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h103, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
        · linarith only [h102, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi0]
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
      · rcases p0_3 (m.d 0 3) (by simp) with h115 | h115
        · rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 0 5) (by simp) with h117 | h117
            · linarith only [h117, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h114, h117, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h116, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 0 5) (by simp) with h122 | h122
            · linarith only [h122, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h114, h122, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h126 | h126
        · rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
          · rcases p0_3 (m.d 0 5) (by simp) with h128 | h128
            · linarith only [h128, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h126, h128, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h127, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · rcases p0_3 (m.d 0 5) (by simp) with h133 | h133
            · linarith only [h133, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h133, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h132, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h137 | h137
    · rcases p0_3 (m.d 0 2) (by simp) with h138 | h138
      · linarith only [h138, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h140 | h140
        · rcases p0_3 (m.d 0 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 0 5) (by simp) with h142 | h142
            · linarith only [h142, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h137, h142, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h137, h147, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h151 | h151
      · linarith only [h151, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h153 | h153
        · rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
          · rcases p0_3 (m.d 0 5) (by simp) with h155 | h155
            · linarith only [h137, h155, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h153, h155, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · linarith only [h160, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h160, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h159, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h164 | h164
    · rcases p0_3 (m.d 0 2) (by simp) with h165 | h165
      · rcases p0_3 (m.d 0 3) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 0 5) (by simp) with h169 | h169
            · linarith only [h169, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h164, h169, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h168, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h173 | h173
        · linarith only [h173, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 0 5) (by simp) with h176 | h176
            · linarith only [h165, h176, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h164, h176, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h175, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h180 | h180
      · rcases p0_3 (m.d 0 3) (by simp) with h181 | h181
        · linarith only [h181, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h183 | h183
          · rcases p0_3 (m.d 0 5) (by simp) with h184 | h184
            · linarith only [h164, h184, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h180, h184, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h183, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h188 | h188
        · linarith only [h188, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h190 | h190
          · rcases p0_3 (m.d 0 5) (by simp) with h191 | h191
            · linarith only [h180, h191, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h191, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h190, hlam, p0_0]
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
    linarith only [hlam, hphi, ht45, p0_1, u4ehi0, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 4 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h2, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h2, h5, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h10, h2, h4, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, h2, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h15 | h15
              · linarith only [h1, h15, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h17 | h17
                · linarith only [h17, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h17, h2, h4, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h20 | h20
          · rcases m.htr 0 2 4 (by decide) (by decide) with h21 | h21
            · linarith only [h21, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h2, h20, h23, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                · linarith only [h25, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h2, h25, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h2, h20, h25, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
            · linarith only [h1, h20, h30, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
              · linarith only [h1, h32, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                · linarith only [h34, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
                  · linarith only [h0, h2, h20, h34, h36, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                    · linarith only [h0, h30, h38, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                      · linarith only [h1, h20, h32, h40, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                        · linarith only [h1, h2, h34, h42, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                          · linarith only [h1, h2, h34, h40, h44, hc13, hc34, hlam, hphi]
                          · linarith only [h1, h2, h36, h44, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h47 | h47
      · linarith only [h47, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 2 3 (by decide) (by decide) with h50 | h50
          · linarith only [h0, h1, h50, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h52 | h52
            · linarith only [h0, h1, h52, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h54 | h54
              · linarith only [h54, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h56 | h56
                · linarith only [h56, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h1, h49, h54, h56, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h59 | h59
          · linarith only [h0, h1, h59, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h61 | h61
            · linarith only [h0, h61, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
              · linarith only [h63, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
                · linarith only [h65, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                  · linarith only [h0, h1, h59, h63, h65, h67, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                    · linarith only [h0, h61, h69, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h1, h63, h67, h71, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h71, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h74 | h74
    · rcases m.htr 0 1 4 (by decide) (by decide) with h75 | h75
      · linarith only [h75, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
        · rcases m.htr 0 2 3 (by decide) (by decide) with h78 | h78
          · rcases m.htr 0 2 4 (by decide) (by decide) with h79 | h79
            · linarith only [h79, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h81 | h81
              · linarith only [h0, h74, h79, h81, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h83 | h83
                · linarith only [h83, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h0, h77, h79, h83, hlam]
          · linarith only [h0, h74, h78, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h87 | h87
          · rcases m.htr 0 2 4 (by decide) (by decide) with h88 | h88
            · linarith only [h88, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
              · linarith only [h74, h90, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
                · linarith only [h92, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h0, h74, h88, h90, h92, h96, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h0, h74, h88, h92, h98, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                          · linarith only [h0, h100, h74, h88, h92, h96, hc13, hc34, hlam, hphi]
                          · linarith only [h100, h74, h75, h94, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                      · linarith only [h103, h74, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                        · linarith only [h0, h105, h74, h88, h92, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h0, h103, h107, h74, h88, h92, hc13, hc34, hlam, hphi]
                          · linarith only [h107, h74, h75, h94, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h74, h87, h94, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h74, h87, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h112 | h112
      · linarith only [h112, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h114 | h114
        · rcases m.htr 0 2 3 (by decide) (by decide) with h115 | h115
          · rcases m.htr 0 2 4 (by decide) (by decide) with h116 | h116
            · linarith only [h116, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h118 | h118
              · linarith only [h115, h116, h118, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
                · linarith only [h120, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h114, h115, h116, h120, h74, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h123 | h123
            · linarith only [h123, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h125 | h125
              · linarith only [h125, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h127 | h127
                · linarith only [h127, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · linarith only [h0, h114, h115, h125, h127, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h130 | h130
          · rcases m.htr 0 2 4 (by decide) (by decide) with h131 | h131
            · linarith only [h131, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h133 | h133
              · linarith only [h130, h131, h133, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                · linarith only [h135, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                            · linarith only [h130, h131, h133, h135, h137, h139, h141, h142, h74, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h144 | h144
                              · linarith only [h130, h131, h135, h137, h139, h141, h144, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                                · linarith only [h130, h131, h135, h142, h146, hc23, hc34, hlam, hphi]
                                · linarith only [h130, h131, h137, h139, h141, h146, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h130, h131, h138, h141, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h133, h139, h140, h74, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                          · linarith only [h130, h131, h135, h139, h152, hc23, hc34, hlam, hphi]
                          · linarith only [h130, h131, h138, h152, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                          · linarith only [h130, h131, h135, h139, h155, hc23, hc34, hlam, hphi]
                          · linarith only [h130, h131, h138, h155, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                      · linarith only [h133, h137, h138, h158, h74, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                          · linarith only [h130, h131, h135, h158, h161, hc23, hc34, hlam, hphi]
                          · linarith only [h137, h138, h160, h161, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                          · linarith only [h130, h131, h135, h158, h164, hc23, hc34, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                            · linarith only [h130, h166, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                              · linarith only [h130, h131, h135, h168, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
                                · linarith only [h0, h138, h164, h166, h170, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h130, h131, h170, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h130, h137, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
            · linarith only [h130, h174, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h176 | h176
              · linarith only [h176, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                · linarith only [h178, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                            · linarith only [h0, h130, h176, h180, h185, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h130, h180, h182, h185, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                            · linarith only [h0, h130, h176, h180, h188, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h130, h182, h184, h188, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h130, h176, h182, h183, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h193 | h193
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                            · linarith only [h178, h182, h192, h193, h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
                                · linarith only [h178, h181, h197, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                · linarith only [h0, h174, h182, h192, h193, h197, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h130, h182, h192, h196, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h182, h192, h193, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                            · linarith only [h0, h130, h176, h180, h203, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                              · linarith only [h180, h192, h205, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                                · linarith only [h178, h181, h207, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                · linarith only [h0, h174, h202, h207, hc01, hc14, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                            · linarith only [h180, h182, h202, h210, hc45, hlam, hphi, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                              · linarith only [h180, h192, h212, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                                · linarith only [h0, h130, h180, h182, h202, h214, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                                  · linarith only [h0, h130, h180, h182, h202, h216, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h0, h130, h180, h182, h216, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h130, h180, h181, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
                    · linarith only [h0, h174, h180, h220, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h222 | h222
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                                  · linarith only [h178, h222, h228, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                  · linarith only [h0, h130, h176, h224, h228, hc01, hc14, hlam, hphi]
                                · linarith only [h0, h220, h227, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h180, h223, h226, hlam]
                            · linarith only [h178, h180, h222, h224, h225, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h236 | h236
                                · linarith only [h112, h224, h236, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h0, h220, h236, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h180, h223, h235, hlam]
                            · linarith only [h180, h222, h234, hlam]
                        · linarith only [h0, h130, h176, h222, h223, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                            · linarith only [h178, h222, h242, h243, h244, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · linarith only [h0, h180, h244, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h222, h242, h243, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                            · linarith only [h178, h222, h248, h249, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · linarith only [h0, h180, h249, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
                            · linarith only [h222, h252, h74, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h180, h252, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT4_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h3, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h7, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h13, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h12, h6, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h18 | h18
            · rcases m.htr 0 3 4 (by decide) (by decide) with h19 | h19
              · linarith only [h19, h3, h4, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h22, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h21, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h18, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 0 3 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h27, h3, h31, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h33, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h27, h33, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h30, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h27, h29, h3, hlam]
            · linarith only [h28, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
            · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
              · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                  · linarith only [h0, h3, h39, h42, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                    · linarith only [h0, h27, h39, h44, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                      · linarith only [h1, h44, h46, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h39, h46, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h27, h41, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                  · linarith only [h0, h3, h39, h51, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                    · linarith only [h0, h27, h39, h53, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                      · linarith only [h1, h53, h55, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h39, h55, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3, h40, h50, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h0, h39, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h61 | h61
      · rcases m.htr 0 2 3 (by decide) (by decide) with h62 | h62
        · rcases m.htr 0 2 4 (by decide) (by decide) with h63 | h63
          · linarith only [h0, h1, h63, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h65 | h65
            · rcases m.htr 0 3 4 (by decide) (by decide) with h66 | h66
              · linarith only [h0, h1, h62, h66, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
                · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                  · linarith only [h0, h69, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h62, h69, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h1, h68, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · linarith only [h62, h65, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
          · linarith only [h0, h1, h74, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h76 | h76
            · rcases m.htr 0 3 4 (by decide) (by decide) with h77 | h77
              · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                  · linarith only [h0, h62, h79, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                    · linarith only [h0, h1, h74, h76, h77, h81, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                      · linarith only [h0, h1, h77, h83, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h76, h83, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1, h78, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                  · linarith only [h0, h62, h76, h88, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                    · linarith only [h0, h1, h74, h76, h90, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h1, h92, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · linarith only [h76, h92, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1, h87, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · linarith only [h0, h76, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h61, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
    · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
      · rcases m.htr 0 2 3 (by decide) (by decide) with h100 | h100
        · rcases m.htr 0 2 4 (by decide) (by decide) with h101 | h101
          · rcases m.htr 0 2 5 (by decide) (by decide) with h102 | h102
            · rcases m.htr 0 3 4 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 4 5 (by decide) (by decide) with h104 | h104
                · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                          · linarith only [h100, h109, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h103, h109, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h100, h103, h108, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h107, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h101, h106, h98, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h100, h105, h98, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h104, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                        · linarith only [h100, h103, h121, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                          · linarith only [h100, h123, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                            · linarith only [h0, h118, h121, h125, h98, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h125, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h120, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h101, h119, h98, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h100, h118, h98, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h103, h117, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h102, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h101, h98, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h134 | h134
          · rcases m.htr 0 2 5 (by decide) (by decide) with h135 | h135
            · rcases m.htr 0 3 4 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h143 | h143
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                              · linarith only [h0, h100, h139, h144, h98, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h142, h144, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h100, h139, h142, h143, h98, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h0, h100, h136, h139, h142, h98, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h100, h136, h138, h139, h141, h98, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h100, h138, h139, h140, h98, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h100, h138, h139, h98, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                              · linarith only [h152, h157, h98, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h157, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h138, h156, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h138, h152, h155, h98, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h136, h138, h152, h154, h98, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h152, h153, h98, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h100, h134, h152, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h137, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h0, h100, h136, h98, hlam]
            · linarith only [h0, h135, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h134, h98, hlam]
      · linarith only [h98, h99, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h170 | h170
      · rcases m.htr 0 2 3 (by decide) (by decide) with h171 | h171
        · rcases m.htr 0 2 4 (by decide) (by decide) with h172 | h172
          · rcases m.htr 0 2 5 (by decide) (by decide) with h173 | h173
            · rcases m.htr 0 3 4 (by decide) (by decide) with h174 | h174
              · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                          · linarith only [h171, h180, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h174, h180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h171, h174, h179, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h177, h178, h98, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h170, h172, h177, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h0, h170, h171, h176, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h170, h175, h98, hc15, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h188 | h188
                · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                          · linarith only [h171, h174, h193, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
                            · linarith only [h171, h195, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h195, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                          · linarith only [h171, h174, h198, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                            · linarith only [h171, h200, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h200, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h191, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h172, h190, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h170, h171, h189, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h174, h188, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h173, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h208 | h208
            · rcases m.htr 0 3 4 (by decide) (by decide) with h209 | h209
              · linarith only [h171, h172, h209, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h214 | h214
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                          · linarith only [h171, h209, h216, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                            · linarith only [h171, h172, h212, h215, h216, h218, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h218, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                          · linarith only [h171, h215, h221, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h223 | h223
                            · linarith only [h171, h172, h223, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h223, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h214, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                        · linarith only [h212, h213, h228, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                          · linarith only [h171, h172, h228, h230, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                            · linarith only [h171, h172, h232, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h0, h170, h213, h227, h230, h232, hc23, hc25, hc34, hlam, hphi, u5elo3]
                      · linarith only [h0, h227, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h170, h171, h212, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h172, h211, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h171, h208, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h239 | h239
          · rcases m.htr 0 2 5 (by decide) (by decide) with h240 | h240
            · rcases m.htr 0 3 4 (by decide) (by decide) with h241 | h241
              · rcases m.htr 0 4 5 (by decide) (by decide) with h242 | h242
                · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h249 | h249
                              · linarith only [h239, h249, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h249, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h171, h239, h247, h248, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h170, h171, h239, h241, h245, h247, h98, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h170, h171, h239, h241, h243, h245, h246, h98, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h170, h171, h239, h243, h245, h98, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h171, h239, h243, h244, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h261 | h261
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                              · linarith only [h239, h262, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h262, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h243, h257, h261, h98, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h170, h243, h257, h258, h260, h98, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h170, h241, h243, h257, h258, h259, h98, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h257, h258, h98, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h171, h239, h257, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h242, h98, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h171, h239, h241, hlam]
            · linarith only [h240, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h273 | h273
            · rcases m.htr 0 3 4 (by decide) (by decide) with h274 | h274
              · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
                · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h278 | h278
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h281 | h281
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                                · linarith only [h274, h283, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h283, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h170, h239, h275, h278, h281, h282, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h0, h239, h280, h281, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h274, h280, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h274, h279, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h170, h171, h276, h278, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h170, h171, h276, h277, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
                    · linarith only [h0, h170, h239, h276, h292, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                                · linarith only [h274, h299, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h299, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h274, h275, h292, h298, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h292, h296, h297, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h170, h171, h274, h294, h296, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h274, h295, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h170, h294, hc15, hlam, hphi, u5elo2]
                · linarith only [h239, h275, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
                · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h313 | h313
                          · linarith only [h0, h170, h171, h274, h309, h311, h313, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h170, h171, h309, h311, h312, h313, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
                          · linarith only [h309, h312, h316, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h318 | h318
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h319 | h319
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                                · rcases h4bigk with h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h98, hlam, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h239, hlam, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h274, hlam, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht0b, ht5b, p321_1, u0elo3]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    rcases p321_3 (m.d 0 4) (by simp) with h327 | h327
                                    · linarith only [h327, h98, hlam]
                                    · rcases p321_3 (m.d 1 4) (by simp) with h329 | h329
                                      · rcases p321_3 (m.d 2 4) (by simp) with h330 | h330
                                        · linarith only [h310, h330, hlam]
                                        · linarith only [h239, h330, hlam]
                                      · linarith only [h329, h98, hlam]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h0, h170, h239, h311, h312, h318, h320, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h312, hlam, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    rcases p321_3 (m.d 0 4) (by simp) with h337 | h337
                                    · linarith only [h337, h98, hlam]
                                    · linarith only [h308, h337, hlam]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h0, h170, h171, h274, h310, h311, h318, h320, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h310, hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h316, hlam, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    rcases p321_3 (m.d 0 4) (by simp) with h344 | h344
                                    · linarith only [h239, h344, hlam]
                                    · linarith only [h308, h344, hlam]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    rcases p321_3 (m.d 0 4) (by simp) with h347 | h347
                                    · linarith only [h274, h347, hlam]
                                    · rcases p321_3 (m.d 1 4) (by simp) with h349 | h349
                                      · linarith only [h312, h349, hlam]
                                      · linarith only [h349, h98, hlam]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h170, h311, h318, h320, h98, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h0, h170, h239, h311, h318, h320, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h0, h170, h171, h309, h311, h312, h318, h320, hlam, p321_2]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h308, hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h0, h170, h171, h309, h311, h312, h318, h320, hlam, p321_1]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h319, hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [h320, hlam, p321_0]
                                  · have p321_0 := h321c.1
                                    have p321_1 := h321c.2.1
                                    have p321_2 := h321c.2.2.1
                                    have p321_3 := h321c.2.2.2
                                    linarith only [hlam, p321_0]
                                · linarith only [h0, h170, h171, h309, h311, h312, h318, h320, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                              · linarith only [h0, h170, h171, h308, h311, h316, h318, h319, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h0, h171, h318, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h311, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h170, h171, h309, h310, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
                    · linarith only [h0, h170, h239, h309, h366, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h368 | h368
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h369 | h369
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h371 | h371
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h372 | h372
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h373 | h373
                                · rcases h4bigk with h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h98, hlam, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h239, hlam, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h274, hlam, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht0b, ht5b, p374_1, u0elo3]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    rcases p374_3 (m.d 0 4) (by simp) with h380 | h380
                                    · linarith only [h380, h98, hlam]
                                    · rcases p374_3 (m.d 1 4) (by simp) with h382 | h382
                                      · rcases p374_3 (m.d 2 4) (by simp) with h383 | h383
                                        · rcases p374_3 (m.d 3 4) (by simp) with h384 | h384
                                          · linarith only [h369, h384, hlam]
                                          · linarith only [h274, h384, hlam]
                                        · linarith only [h239, h383, hlam]
                                      · linarith only [h382, h98, hlam]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h366, hlam, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h0, h170, h171, h274, h366, h368, h370, h371, h373, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    rcases p374_3 (m.d 0 4) (by simp) with h392 | h392
                                    · linarith only [h392, h98, hlam]
                                    · linarith only [h308, h392, hlam]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    rcases p374_3 (m.d 0 4) (by simp) with h395 | h395
                                    · linarith only [h239, h395, hlam]
                                    · rcases p374_3 (m.d 1 4) (by simp) with h397 | h397
                                      · linarith only [h366, h397, hlam]
                                      · linarith only [h397, h98, hlam]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h170, h368, h370, h371, h373, h98, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h0, h170, h171, h274, h368, h370, h371, h373, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h0, h170, h366, h368, h371, h373, hlam, p374_2]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h0, h170, h171, h274, h368, h369, h371, h373, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p374_1]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h369, hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h370, hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    rcases p374_3 (m.d 0 4) (by simp) with h408 | h408
                                    · linarith only [h274, h408, hlam]
                                    · linarith only [h308, h408, hlam]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h308, hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h170, h368, h371, h373, hc14, hlam, hphi, ht0b, ht45, ht5b, p374_1, u0elo0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h372, hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [h373, hlam, p374_0]
                                  · have p374_0 := h374c.1
                                    have p374_1 := h374c.2.1
                                    have p374_2 := h374c.2.2.1
                                    have p374_3 := h374c.2.2.2
                                    linarith only [hlam, p374_0]
                                · linarith only [h0, h171, h274, h373, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h0, h308, h366, h372, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h0, h170, h171, h274, h309, h368, h369, h371, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h309, h369, h370, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
                          · linarith only [h0, h170, h309, h368, h369, h420, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h170, h309, h368, h420, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h170, h368, hc15, hlam, hphi, u5elo2]
                · linarith only [h171, h274, h308, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h0, h170, h273, hc15, hlam, hphi, u5elo2]
      · linarith only [h170, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT4_H_L_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
        · linarith only [h2, h4, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 2 4 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h2, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h2, h9, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h11 | h11
                · linarith only [h0, h11, h2, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h2, h6, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h15, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h15, h17, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h0, h15, h17, h2, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
            · linarith only [h1, h20, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
              · linarith only [h1, h2, h22, h6, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
                · linarith only [h1, h2, h24, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h1, h2, h26, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h28, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h2, h28, h30, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                        · linarith only [h0, h20, h32, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h1, h22, h30, h34, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                            · linarith only [h1, h24, h36, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                              · linarith only [h1, h26, h38, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                                · linarith only [h1, h2, h28, h30, h32, h40, hc12, hc24, hlam, hphi]
                                · linarith only [h1, h2, h30, h40, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h43 | h43
      · linarith only [h43, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
        · linarith only [h1, h45, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h47 | h47
          · linarith only [h0, h1, h47, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h49 | h49
            · linarith only [h0, h1, h49, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h51 | h51
              · linarith only [h0, h1, h51, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h53 | h53
                · linarith only [h53, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h53, h55, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                    · linarith only [h57, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h1, h47, h53, h57, h59, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h61 | h61
                        · linarith only [h0, h49, h61, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                          · linarith only [h0, h51, h63, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                            · linarith only [h0, h1, h53, h59, h65, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h65, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h68 | h68
    · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
      · linarith only [h69, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h71 | h71
        · linarith only [h0, h71, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h73 | h73
          · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
            · linarith only [h74, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h76 | h76
              · linarith only [h74, h76, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
                · linarith only [h0, h68, h74, h78, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
                  · linarith only [h0, h68, h74, h80, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
                    · linarith only [h82, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                            · linarith only [h0, h68, h74, h78, h82, h87, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                              · linarith only [h68, h80, h82, h89, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                                · linarith only [h0, h68, h74, h82, h84, h87, h91, hc23, hc34, hlam, hphi]
                                · linarith only [h68, h69, h84, h91, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h68, h74, h84, h85, h86, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                          · linarith only [h0, h68, h76, h84, h85, h95, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
                            · linarith only [h68, h97, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                              · linarith only [h0, h68, h74, h82, h99, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                                · linarith only [h0, h101, h68, h74, h82, h84, h97, hc23, hc34, hlam, hphi]
                                · linarith only [h101, h68, h69, h84, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h73, h74, h82, h84, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h68, h73, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
      · linarith only [h106, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h108 | h108
        · linarith only [h0, h108, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h110 | h110
          · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
            · linarith only [h111, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h113 | h113
              · linarith only [h111, h113, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h115 | h115
                · linarith only [h110, h111, h115, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h110, h111, h117, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h119, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                                  · linarith only [h110, h111, h115, h119, h121, h124, h126, h127, h68, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                                    · linarith only [h110, h111, h117, h119, h121, h124, h126, h129, h68, hc01, hc12, hlam, hphi]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                                      · linarith only [h110, h111, h119, h127, h131, hc23, hc34, hlam, hphi]
                                      · linarith only [h110, h111, h121, h124, h126, h131, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h110, h111, h122, h126, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h115, h124, h125, h68, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                              · linarith only [h117, h124, h136, h68, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                                · linarith only [h110, h111, h119, h124, h138, hc23, hc34, hlam, hphi]
                                · linarith only [h110, h111, h122, h138, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h110, h111, h122, h123, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h110, h113, h122, h142, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                            · linarith only [h115, h121, h122, h144, h68, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                              · linarith only [h117, h144, h146, h68, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                                · linarith only [h110, h111, h119, h144, h148, hc23, hc34, hlam, hphi]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                                  · linarith only [h110, h150, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                                    · linarith only [h110, h111, h119, h146, h152, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                                      · linarith only [h106, h110, h111, h148, h150, h154, hc23, hc34, hlam, hphi]
                                      · linarith only [h110, h111, h154, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h110, h121, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h158 | h158
            · linarith only [h158, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h160 | h160
              · linarith only [h110, h160, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
                · linarith only [h162, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                  · linarith only [h162, h164, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h166 | h166
                    · linarith only [h166, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                                  · linarith only [h0, h110, h162, h168, h174, hc01, hc12, hlam, hphi]
                                  · linarith only [h0, h110, h168, h171, h174, hc01, hc12, hlam, hphi]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                                  · linarith only [h0, h110, h162, h168, h177, hc01, hc12, hlam, hphi]
                                  · linarith only [h0, h110, h168, h171, h177, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h110, h162, h171, h172, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                              · linarith only [h0, h110, h164, h171, h181, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                                  · linarith only [h171, h184, h68, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                                    · linarith only [h168, h181, h186, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                                      · linarith only [h166, h169, h188, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                      · linarith only [h0, h158, h171, h183, h188, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                                  · linarith only [h0, h110, h162, h168, h181, h191, hc01, hc35, hlam, hphi, ht12, ht23]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                                    · linarith only [h0, h110, h164, h168, h193, hc01, hc12, hlam, hphi]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                                      · linarith only [h169, h183, h195, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h197 | h197
                                        · linarith only [h171, h183, h197, h68, hc01, hc34, hlam, hphi, ht12, ht23]
                                        · linarith only [h0, h110, h168, h171, h197, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h110, h168, h170, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h0, h110, h168, h169, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                        · linarith only [h0, h158, h168, h202, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                          · linarith only [h0, h160, h168, h204, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h208 | h208
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h210 | h210
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h211 | h211
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h212 | h212
                                        · linarith only [h166, h206, h212, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                        · linarith only [h0, h110, h162, h208, h212, hc01, hc14, hlam, hphi]
                                      · linarith only [h202, h208, h211, hlam]
                                    · linarith only [h168, h207, h210, hlam]
                                  · linarith only [h0, h110, h164, h168, h207, h209, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h219 | h219
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h220 | h220
                                      · linarith only [h0, h110, h162, h206, h208, h220, hc01, hc24, hlam, hphi, ht12]
                                      · linarith only [h0, h202, h220, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                    · linarith only [h168, h207, h219, hlam]
                                  · linarith only [h0, h110, h164, h168, h206, h207, h218, hc01, hc14, hlam, hphi]
                              · linarith only [h0, h110, h162, h206, h207, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
                              · linarith only [h0, h110, h164, h206, h226, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
                                  · linarith only [h166, h206, h228, h229, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                                  · linarith only [h0, h168, h229, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                                  · linarith only [h0, h168, h206, h232, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h168, h232, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT4_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.1
  have h5ehi := hb5.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h10, h11, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                          · linarith only [h0, h11, h14, h2, h4, h5, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                            · linarith only [h11, h13, h16, h6, h8, hlam]
                            · linarith only [h0, h13, h16, h2, h4, h5, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h10, h11, h13, h19, h2, h4, h5, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h10, h13, h19, h6, h8, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h1, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                        · linarith only [h10, h24, h6, h8, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                          · linarith only [h0, h2, h26, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                            · linarith only [h22, h28, h7, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                              · linarith only [h24, h28, h30, h7, h8, hc23, hc34, hlam, hphi]
                              · rcases h4bigk with h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 4) (by simp) with h34 | h34
                                  · rcases p32_3 (m.d 1 4) (by simp) with h35 | h35
                                    · linarith only [h1, h35, hlam]
                                    · rcases p32_3 (m.d 2 4) (by simp) with h37 | h37
                                      · linarith only [h3, h37, hlam]
                                      · rcases p32_3 (m.d 3 4) (by simp) with h39 | h39
                                        · linarith only [h39, h4, hlam]
                                        · linarith only [h10, h39, hlam]
                                  · linarith only [h1, h34, hlam]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h26, h30, h5, h7, h8, hlam, p32_2]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 4) (by simp) with h44 | h44
                                  · rcases p32_3 (m.d 1 4) (by simp) with h45 | h45
                                    · linarith only [h1, h45, hlam]
                                    · rcases p32_3 (m.d 2 4) (by simp) with h47 | h47
                                      · linarith only [h3, h47, hlam]
                                      · rcases p32_3 (m.d 3 4) (by simp) with h49 | h49
                                        · linarith only [h4, h49, hlam]
                                        · rcases p32_3 (m.d 4 5) (by simp) with h51 | h51
                                          · linarith only [h5, h51, hlam]
                                          · linarith only [h30, h51, hlam]
                                  · linarith only [h4, h44, hlam]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h0, h2, h24, h26, h30, h4, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h1, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h24, h26, h7, h8, hc23, hc35, hlam, hphi, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h10, hlam, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h22, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h3, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h7, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h24, hlam, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h28, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h4, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h0, h2, h30, h4, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h0, h2, h24, h30, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h30, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h5, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 4) (by simp) with h72 | h72
                                  · rcases p32_3 (m.d 1 4) (by simp) with h73 | h73
                                    · linarith only [h73, hlam, p32_0]
                                    · rcases p32_3 (m.d 2 4) (by simp) with h75 | h75
                                      · linarith only [h28, h75, hlam]
                                      · rcases p32_3 (m.d 3 4) (by simp) with h77 | h77
                                        · linarith only [h30, h77, hlam]
                                        · linarith only [h10, h77, hlam]
                                  · linarith only [h1, h72, hlam]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 4) (by simp) with h81 | h81
                                  · rcases p32_3 (m.d 1 4) (by simp) with h82 | h82
                                    · linarith only [h22, h82, hlam]
                                    · linarith only [h7, h82, hlam]
                                  · linarith only [h3, h81, hlam]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h0, h10, h2, h4, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                  · linarith only [h7, h88, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                    · linarith only [h6, h7, h90, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                      · linarith only [h1, h92, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                        · linarith only [h0, h2, h4, h5, h6, h7, h92, h94, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                          · linarith only [h6, h96, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                            · linarith only [h0, h2, h4, h6, h7, h92, h94, h98, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h2, h4, h5, h6, h7, h98, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                  · linarith only [h102, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                      · linarith only [h0, h101, h105, h2, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                          · linarith only [h0, h108, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                            · linarith only [h101, h108, h110, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                              · linarith only [h101, h107, h108, h110, h112, h6, hlam]
                              · linarith only [h0, h101, h108, h112, h2, h4, h5, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h101, h107, h2, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h101, h104, h6, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h117, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h1, h120, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                          · linarith only [h0, h123, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
                            · linarith only [h0, h125, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                              · linarith only [h101, h125, h127, hc12, hc34, hlam, hphi, ht23]
                              · rcases h4bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  rcases p129_3 (m.d 0 4) (by simp) with h131 | h131
                                  · rcases p129_3 (m.d 1 4) (by simp) with h132 | h132
                                    · linarith only [h1, h132, hlam]
                                    · rcases p129_3 (m.d 2 4) (by simp) with h134 | h134
                                      · linarith only [h134, h3, hlam]
                                      · linarith only [h101, h134, hlam]
                                  · linarith only [h1, h131, hlam]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  rcases p129_3 (m.d 0 4) (by simp) with h138 | h138
                                  · rcases p129_3 (m.d 1 4) (by simp) with h139 | h139
                                    · linarith only [h1, h139, hlam]
                                    · rcases p129_3 (m.d 2 4) (by simp) with h141 | h141
                                      · linarith only [h141, h3, hlam]
                                      · rcases p129_3 (m.d 3 4) (by simp) with h143 | h143
                                        · linarith only [h143, h4, hlam]
                                        · rcases p129_3 (m.d 4 5) (by simp) with h145 | h145
                                          · linarith only [h145, h5, hlam]
                                          · linarith only [h125, h145, hlam]
                                  · linarith only [h138, h3, hlam]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h119, h123, h127, h5, h6, hlam, p129_2]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h0, h101, h122, h123, h127, h2, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h1, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h101, hlam, p129_1]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h119, h123, h127, h6, hc34, hc45, hlam, hphi, p129_1]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h120, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h3, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h0, h101, h122, h123, h127, h2, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h0, h122, h123, h127, h2, h4, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h125, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h4, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h119, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h122, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h127, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h5, hlam, p129_0]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  rcases p129_3 (m.d 0 4) (by simp) with h167 | h167
                                  · rcases p129_3 (m.d 1 4) (by simp) with h168 | h168
                                    · linarith only [h168, hlam, p129_0]
                                    · rcases p129_3 (m.d 2 4) (by simp) with h170 | h170
                                      · linarith only [h125, h170, hlam]
                                      · linarith only [h101, h170, hlam]
                                  · linarith only [h1, h167, hlam]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [h0, h101, h2, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  rcases p129_3 (m.d 0 4) (by simp) with h175 | h175
                                  · rcases p129_3 (m.d 1 4) (by simp) with h176 | h176
                                    · linarith only [h120, h176, hlam]
                                    · linarith only [h119, h176, hlam]
                                  · linarith only [h175, h4, hlam]
                                · have p129_0 := h129c.1
                                  have p129_1 := h129c.2.1
                                  have p129_2 := h129c.2.2.1
                                  have p129_3 := h129c.2.2.2
                                  linarith only [hlam, p129_0]
                        · linarith only [h119, h122, h6, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                      · linarith only [h1, h182, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                          · linarith only [h0, h185, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h119, h184, h185, h6, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                          · linarith only [h184, h188, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h190 | h190
                            · linarith only [h0, h184, h190, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h192 | h192
                              · linarith only [h184, h190, h192, h6, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h184, h192, h2, h4, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc24, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc14, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT4_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h10, h16, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                                    · linarith only [h0, h10, h13, h16, h18, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                                      · linarith only [h0, h10, h13, h16, h20, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · linarith only [h0, h10, h13, h15, h20, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                                  · linarith only [h0, h10, h23, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                                    · linarith only [h0, h13, h15, h23, h25, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                      · linarith only [h0, h15, h27, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                        · linarith only [h13, h15, h29, hlam]
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
                                            rcases p31_3 (m.d 0 5) (by simp) with h33 | h33
                                            · rcases p31_3 (m.d 1 5) (by simp) with h34 | h34
                                              · linarith only [h3, h34, hlam]
                                              · rcases p31_3 (m.d 2 5) (by simp) with h36 | h36
                                                · linarith only [h36, h6, hlam]
                                                · rcases p31_3 (m.d 3 5) (by simp) with h38 | h38
                                                  · linarith only [h38, h8, hlam]
                                                  · rcases p31_3 (m.d 4 5) (by simp) with h40 | h40
                                                    · linarith only [h40, h9, hlam]
                                                    · linarith only [h15, h40, hlam]
                                            · linarith only [h3, h33, hlam]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            rcases p31_3 (m.d 0 5) (by simp) with h44 | h44
                                            · rcases p31_3 (m.d 1 5) (by simp) with h45 | h45
                                              · linarith only [h3, h45, hlam]
                                              · linarith only [h12, h45, hlam]
                                            · linarith only [h44, h6, hlam]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            rcases p31_3 (m.d 0 5) (by simp) with h49 | h49
                                            · rcases p31_3 (m.d 1 5) (by simp) with h50 | h50
                                              · linarith only [h3, h50, hlam]
                                              · linarith only [h14, h50, hlam]
                                            · linarith only [h49, h8, hlam]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h0, h13, h15, h23, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h3, hlam, p31_0]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [hlam, p31_0]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h27, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p31_1, u4ehi2]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h0, h10, h14, h25, h27, hc01, hlam, hphi, ht0b, ht45, ht5b, p31_1, u4ehi2]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h15, hlam, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h6, hlam, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h12, hlam, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [hlam, p31_0]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h25, hlam, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h27, hlam, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h8, hlam, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h14, hlam, p31_1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h0, h27, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p31_1, u4ehi2]
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
                                            linarith only [h9, hlam, p31_0]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi1]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h0, h27, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p31_1, u4ehi2]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi3]
                                          · have p31_0 := h31c.1
                                            have p31_1 := h31c.2.1
                                            have p31_2 := h31c.2.2.1
                                            have p31_3 := h31c.2.2.2
                                            linarith only [hlam, p31_0]
                              · linarith only [h0, h13, h14, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
                              · linarith only [h0, h13, h4, h7, h76, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                                  · linarith only [h0, h10, h13, h79, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h81 | h81
                                    · linarith only [h10, h76, h81, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                                      · linarith only [h0, h11, h83, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h2, h78, h83, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                                  · linarith only [h10, h13, h86, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                                    · linarith only [h0, h10, h13, h4, h7, h76, h88, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                                      · linarith only [h11, h78, h90, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                                        · linarith only [h0, h11, h4, h7, h78, h92, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                        · rcases h5bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [hlam, p94_0]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            rcases p94_3 (m.d 0 5) (by simp) with h96 | h96
                                            · rcases p94_3 (m.d 1 5) (by simp) with h97 | h97
                                              · linarith only [h3, h97, hlam]
                                              · rcases p94_3 (m.d 2 5) (by simp) with h99 | h99
                                                · linarith only [h6, h99, hlam]
                                                · rcases p94_3 (m.d 3 5) (by simp) with h101 | h101
                                                  · linarith only [h101, h8, hlam]
                                                  · linarith only [h101, h76, hlam]
                                            · linarith only [h3, h96, hlam]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            rcases p94_3 (m.d 0 5) (by simp) with h105 | h105
                                            · rcases p94_3 (m.d 1 5) (by simp) with h106 | h106
                                              · linarith only [h106, h3, hlam]
                                              · linarith only [h106, h12, hlam]
                                            · linarith only [h105, h6, hlam]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            rcases p94_3 (m.d 0 5) (by simp) with h110 | h110
                                            · rcases p94_3 (m.d 1 5) (by simp) with h111 | h111
                                              · linarith only [h111, h3, hlam]
                                              · rcases p94_3 (m.d 2 5) (by simp) with h113 | h113
                                                · linarith only [h113, h6, hlam]
                                                · rcases p94_3 (m.d 3 5) (by simp) with h115 | h115
                                                  · linarith only [h115, h8, hlam]
                                                  · rcases p94_3 (m.d 4 5) (by simp) with h117 | h117
                                                    · linarith only [h117, h9, hlam]
                                                    · linarith only [h117, h92, hlam]
                                            · linarith only [h110, h8, hlam]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h0, h11, h4, h7, h78, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p94_1, u4ehi2]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h3, hlam, p94_0]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [hlam, p94_0]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h3, h90, hc01, hlam, hphi, ht0b, ht45, ht5b, p94_1, u4ehi2]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h76, hlam, p94_0]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h78, hlam, p94_1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h6, hlam, p94_1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h12, hlam, p94_1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [hlam, p94_0]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h88, hlam, p94_1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h90, hlam, p94_1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h8, hlam, p94_1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht5b, p94_1, u5ehi1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h0, h4, h8, h90, hc01, hlam, hphi, ht0b, ht45, ht5b, p94_1, u4ehi2]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [hlam, p94_0]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h92, hlam, p94_1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h9, hlam, p94_0]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h0, h4, h7, h78, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p94_1, u4ehi1]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h0, h4, h7, h9, h90, hc01, hlam, hphi, ht0b, ht45, ht5b, p94_1, u4ehi2]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p94_1, u5ehi3]
                                          · have p94_0 := h94c.1
                                            have p94_1 := h94c.2.1
                                            have p94_2 := h94c.2.2.1
                                            have p94_3 := h94c.2.2.2
                                            linarith only [hlam, p94_0]
                          · linarith only [h0, h11, h12, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h143 | h143
                          · linarith only [h0, h11, h143, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                            · linarith only [h0, h10, h11, h145, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                              · linarith only [h0, h10, h11, h147, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                                  · linarith only [h0, h10, h11, h145, h150, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                                    · linarith only [h10, h143, h147, h152, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                                        · rcases h5bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            rcases p156_3 (m.d 0 5) (by simp) with h158 | h158
                                            · rcases p156_3 (m.d 1 5) (by simp) with h159 | h159
                                              · linarith only [h159, h3, hlam]
                                              · rcases p156_3 (m.d 2 5) (by simp) with h161 | h161
                                                · linarith only [h161, h6, hlam]
                                                · linarith only [h143, h161, hlam]
                                            · linarith only [h158, h3, hlam]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h0, h10, h143, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h0, h10, h143, h152, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            rcases p156_3 (m.d 0 5) (by simp) with h167 | h167
                                            · rcases p156_3 (m.d 1 5) (by simp) with h168 | h168
                                              · linarith only [h168, h3, hlam]
                                              · linarith only [h149, h168, hlam]
                                            · linarith only [h167, h9, hlam]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h3, hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h143, hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h147, hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p156_1, u4ehi4]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h6, hlam, p156_1]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, p156_1, u5ehi1]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h152, hlam, p156_1]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h0, h150, h154, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p156_1, u4ehi4]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h8, hlam, p156_1]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h0, h10, h143, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p156_1]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht5b, p156_1, u5ehi2]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h0, h155, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p156_1, u4ehi4]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h9, hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h149, hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h154, hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [h155, hlam, p156_0]
                                          · have p156_0 := h156c.1
                                            have p156_1 := h156c.2.1
                                            have p156_2 := h156c.2.2.1
                                            have p156_3 := h156c.2.2.2
                                            linarith only [hlam, p156_0]
                                        · linarith only [h149, h150, h155, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                      · linarith only [h0, h10, h11, h154, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                                  · linarith only [h10, h11, h194, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
                                    · linarith only [h0, h10, h11, h149, h196, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h198 | h198
                                      · linarith only [h10, h11, h149, h194, h198, hc23, hc34, hlam, hphi]
                                      · linarith only [h0, h10, h11, h198, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                        · linarith only [h0, h10, h201, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                          · linarith only [h0, h10, h203, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h206 | h206
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h207 | h207
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h210 | h210
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                                        · linarith only [h1, h205, h211, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                        · linarith only [h2, h207, h211, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                      · linarith only [h201, h207, h210, hlam]
                                    · linarith only [h10, h206, h209, hlam]
                                  · linarith only [h0, h10, h206, h208, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                                      · linarith only [h0, h207, h217, h219, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h221 | h221
                                        · linarith only [h205, h219, h221, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                        · rcases h5bigk with h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            rcases p223_3 (m.d 0 5) (by simp) with h225 | h225
                                            · rcases p223_3 (m.d 1 5) (by simp) with h226 | h226
                                              · linarith only [h226, h3, hlam]
                                              · rcases p223_3 (m.d 2 5) (by simp) with h228 | h228
                                                · linarith only [h228, h6, hlam]
                                                · linarith only [h203, h228, hlam]
                                            · linarith only [h225, h3, hlam]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            rcases p223_3 (m.d 0 5) (by simp) with h232 | h232
                                            · rcases p223_3 (m.d 1 5) (by simp) with h233 | h233
                                              · linarith only [h233, h3, hlam]
                                              · rcases p223_3 (m.d 2 5) (by simp) with h235 | h235
                                                · linarith only [h235, h6, hlam]
                                                · rcases p223_3 (m.d 3 5) (by simp) with h237 | h237
                                                  · linarith only [h237, h8, hlam]
                                                  · rcases p223_3 (m.d 4 5) (by simp) with h239 | h239
                                                    · linarith only [h239, h9, hlam]
                                                    · linarith only [h219, h239, hlam]
                                            · linarith only [h232, h6, hlam]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            rcases p223_3 (m.d 0 5) (by simp) with h243 | h243
                                            · rcases p223_3 (m.d 1 5) (by simp) with h244 | h244
                                              · linarith only [h244, h3, hlam]
                                              · linarith only [h206, h244, hlam]
                                            · linarith only [h243, h8, hlam]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h0, h201, h219, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p223_1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h3, hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h203, hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h221, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p223_1, u4ehi3]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h207, hlam, p223_1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h6, hlam, p223_1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, p223_1, u5ehi1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h0, h218, h221, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p223_1, u4ehi3]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h219, hlam, p223_1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h8, hlam, p223_1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h206, hlam, p223_1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h218, hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h221, hlam, p223_1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h9, hlam, p223_0]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h0, h207, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p223_1, u4ehi1]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p223_1, u5ehi2]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [h0, h221, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p223_1, u4ehi3]
                                          · have p223_0 := h223c.1
                                            have p223_1 := h223c.2.1
                                            have p223_2 := h223c.2.2.1
                                            have p223_3 := h223c.2.2.2
                                            linarith only [hlam, p223_0]
                                    · linarith only [h0, h10, h205, h218, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h10, h205, h217, hlam]
                              · linarith only [h0, h205, h206, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h272 | h272
                              · linarith only [h0, h205, h272, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h275 | h275
                                  · linarith only [h0, h205, h274, h275, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                                    · linarith only [h0, h10, h272, h275, h277, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                                        · rcases h5bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            rcases p281_3 (m.d 0 5) (by simp) with h283 | h283
                                            · rcases p281_3 (m.d 1 5) (by simp) with h284 | h284
                                              · linarith only [h284, h3, hlam]
                                              · rcases p281_3 (m.d 2 5) (by simp) with h286 | h286
                                                · linarith only [h286, h6, hlam]
                                                · linarith only [h203, h286, hlam]
                                            · linarith only [h283, h3, hlam]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            rcases p281_3 (m.d 0 5) (by simp) with h290 | h290
                                            · rcases p281_3 (m.d 1 5) (by simp) with h291 | h291
                                              · linarith only [h291, h3, hlam]
                                              · rcases p281_3 (m.d 2 5) (by simp) with h293 | h293
                                                · linarith only [h293, h6, hlam]
                                                · rcases p281_3 (m.d 3 5) (by simp) with h295 | h295
                                                  · linarith only [h295, h8, hlam]
                                                  · linarith only [h277, h295, hlam]
                                            · linarith only [h290, h6, hlam]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h0, h10, h277, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            rcases p281_3 (m.d 0 5) (by simp) with h300 | h300
                                            · rcases p281_3 (m.d 1 5) (by simp) with h301 | h301
                                              · linarith only [h3, h301, hlam]
                                              · linarith only [h274, h301, hlam]
                                            · linarith only [h300, h9, hlam]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h3, hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h203, hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h272, hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p281_1, u4ehi4]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h6, hlam, p281_1]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, p281_1, u5ehi1]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h277, hlam, p281_1]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h0, h279, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p281_1, u4ehi4]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h8, hlam, p281_1]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h0, h274, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p281_1, u4ehi4]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht5b, p281_1, u5ehi2]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h0, h280, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p281_1, u4ehi4]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h9, hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h274, hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h279, hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [h280, hlam, p281_0]
                                          · have p281_0 := h281c.1
                                            have p281_1 := h281c.2.1
                                            have p281_2 := h281c.2.2.1
                                            have p281_3 := h281c.2.2.2
                                            linarith only [hlam, p281_0]
                                        · linarith only [h2, h274, h275, h280, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                      · linarith only [h201, h274, h279, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h327 | h327
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h329 | h329
                                      · linarith only [h0, h274, h329, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h331 | h331
                                        · linarith only [h327, h329, h331, hlam]
                                        · rcases h5bigk with h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            rcases p333_3 (m.d 0 5) (by simp) with h335 | h335
                                            · rcases p333_3 (m.d 1 5) (by simp) with h336 | h336
                                              · linarith only [h3, h336, hlam]
                                              · rcases p333_3 (m.d 2 5) (by simp) with h338 | h338
                                                · linarith only [h338, h6, hlam]
                                                · linarith only [h203, h338, hlam]
                                            · linarith only [h3, h335, hlam]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            rcases p333_3 (m.d 0 5) (by simp) with h342 | h342
                                            · rcases p333_3 (m.d 1 5) (by simp) with h343 | h343
                                              · linarith only [h3, h343, hlam]
                                              · rcases p333_3 (m.d 2 5) (by simp) with h345 | h345
                                                · linarith only [h345, h6, hlam]
                                                · rcases p333_3 (m.d 3 5) (by simp) with h347 | h347
                                                  · linarith only [h347, h8, hlam]
                                                  · rcases p333_3 (m.d 4 5) (by simp) with h349 | h349
                                                    · linarith only [h349, h9, hlam]
                                                    · linarith only [h329, h349, hlam]
                                            · linarith only [h342, h6, hlam]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            rcases p333_3 (m.d 0 5) (by simp) with h353 | h353
                                            · rcases p333_3 (m.d 1 5) (by simp) with h354 | h354
                                              · linarith only [h3, h354, hlam]
                                              · rcases p333_3 (m.d 2 5) (by simp) with h356 | h356
                                                · linarith only [h356, h6, hlam]
                                                · linarith only [h328, h356, hlam]
                                            · linarith only [h353, h8, hlam]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h274, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p333_1, u4ehi1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h3, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h203, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h272, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h274, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h6, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h274, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p333_1, u4ehi1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h328, h4, hc01, hlam, hphi, ht0b, ht5b, p333_1, u5ehi3]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h329, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h8, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h274, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p333_1, u4ehi1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h328, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h331, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h9, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h274, hc45, hlam, hphi, p333_1, u4ehi1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p333_1, u5ehi2]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p333_1, u5ehi3]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                    · linarith only [h0, h10, h205, h327, h328, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
                                    · linarith only [h0, h327, h382, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
                                      · linarith only [h0, h274, h384, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h386 | h386
                                        · linarith only [h0, h384, h386, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                        · linarith only [h10, h327, h386, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h9, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                  · linarith only [h8, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                · linarith only [h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
              · linarith only [h6, hc25, hlam, hphi, ht01, ht12, u0ehi1]
            · linarith only [h4, h5, hc24, hlam, hphi, ht01, ht12, u0ehi2]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT4_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
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
        · rcases p0_3 (m.d 3 5) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · rcases m.htr 0 1 5 (by decide) (by decide) with h12 | h12
              · linarith only [h12, hlam, p0_0]
              · linarith only [h11, h12, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h15 | h15
              · linarith only [h15, hlam, p0_0]
              · linarith only [h15, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h18 | h18
            · rcases m.htr 0 1 5 (by decide) (by decide) with h19 | h19
              · linarith only [h19, hlam, p0_0]
              · linarith only [h18, h19, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h22 | h22
              · linarith only [h22, hlam, p0_0]
              · linarith only [h22, hc01, hc15, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · rcases m.htr 0 1 5 (by decide) (by decide) with h27 | h27
              · linarith only [h27, hlam, p0_0]
              · linarith only [h26, h27, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
              · linarith only [h30, hlam, p0_0]
              · linarith only [h30, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h33 | h33
            · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
              · linarith only [h34, hlam, p0_0]
              · linarith only [h33, h34, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
              · linarith only [h37, hlam, p0_0]
              · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
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
    rcases p0_3 (m.d 0 5) (by simp) with h42 | h42
    · linarith only [h42, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h44 | h44
      · rcases p0_3 (m.d 2 5) (by simp) with h45 | h45
        · linarith only [h45, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h47 | h47
          · rcases p0_3 (m.d 4 5) (by simp) with h48 | h48
            · rcases m.htr 0 1 5 (by decide) (by decide) with h49 | h49
              · linarith only [h49, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h42, h49, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
              · linarith only [h42, h52, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h42, h52, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h55 | h55
            · rcases m.htr 0 1 5 (by decide) (by decide) with h56 | h56
              · linarith only [h42, h56, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h42, h56, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h59 | h59
              · linarith only [h42, h59, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h42, h59, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h44, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
    · linarith only [h63, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h65 | h65
      · rcases p0_3 (m.d 2 5) (by simp) with h66 | h66
        · rcases p0_3 (m.d 3 5) (by simp) with h67 | h67
          · linarith only [h67, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · rcases m.htr 0 1 5 (by decide) (by decide) with h70 | h70
              · linarith only [h70, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h63, h70, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h73 | h73
              · linarith only [h63, h73, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h63, h73, hc01, hc15, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h76 | h76
          · linarith only [h76, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · rcases m.htr 0 1 5 (by decide) (by decide) with h79 | h79
              · linarith only [h63, h79, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h63, h79, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
              · linarith only [h63, h82, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h63, h82, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h65, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h86 | h86
    · linarith only [h86, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h88 | h88
      · rcases p0_3 (m.d 2 5) (by simp) with h89 | h89
        · rcases p0_3 (m.d 3 5) (by simp) with h90 | h90
          · rcases p0_3 (m.d 4 5) (by simp) with h91 | h91
            · linarith only [h91, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h93 | h93
              · linarith only [h93, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h86, h93, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h98 | h98
              · linarith only [h86, h98, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h86, h98, hc01, hc15, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h101 | h101
          · rcases p0_3 (m.d 4 5) (by simp) with h102 | h102
            · linarith only [h102, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
              · linarith only [h104, h86, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h104, h86, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h109 | h109
              · linarith only [h109, h86, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h109, h86, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h88, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h113 | h113
    · linarith only [h113, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 5) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 5) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · rcases m.htr 0 1 5 (by decide) (by decide) with h119 | h119
              · linarith only [h115, h119, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h115, h119, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h122 | h122
              · linarith only [h115, h122, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h115, h122, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h125 | h125
            · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
              · linarith only [h115, h126, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h115, h126, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h129 | h129
              · linarith only [h115, h129, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h115, h129, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h133 | h133
        · rcases p0_3 (m.d 3 5) (by simp) with h134 | h134
          · rcases p0_3 (m.d 4 5) (by simp) with h135 | h135
            · rcases m.htr 0 1 5 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 2 5 (by decide) (by decide) with h137 | h137
                · linarith only [h137, hlam, p0_0]
                · linarith only [h135, h137, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h115, h136, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h141 | h141
              · rcases m.htr 0 2 5 (by decide) (by decide) with h142 | h142
                · linarith only [h142, hlam, p0_0]
                · linarith only [h142, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h115, h141, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h146 | h146
            · rcases m.htr 0 1 5 (by decide) (by decide) with h147 | h147
              · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
                · linarith only [h148, hlam, p0_0]
                · linarith only [h146, h148, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h115, h147, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
              · rcases m.htr 0 2 5 (by decide) (by decide) with h153 | h153
                · linarith only [h153, hlam, p0_0]
                · linarith only [h153, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h115, h152, hlam]
        · linarith only [h133, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h158 | h158
    · linarith only [h158, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h160 | h160
      · linarith only [h160, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h162 | h162
        · rcases p0_3 (m.d 3 5) (by simp) with h163 | h163
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · rcases m.htr 0 1 5 (by decide) (by decide) with h165 | h165
              · linarith only [h158, h165, hlam]
              · linarith only [h164, h165, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h168 | h168
              · linarith only [h158, h168, hlam]
              · linarith only [h168, hc01, hc25, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h171 | h171
            · rcases m.htr 0 1 5 (by decide) (by decide) with h172 | h172
              · linarith only [h158, h172, hlam]
              · linarith only [h171, h172, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h175 | h175
              · linarith only [h158, h175, hlam]
              · linarith only [h175, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h162, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h180 | h180
    · linarith only [h180, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h182 | h182
      · rcases p0_3 (m.d 2 5) (by simp) with h183 | h183
        · rcases p0_3 (m.d 3 5) (by simp) with h184 | h184
          · linarith only [h184, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h186 | h186
            · rcases m.htr 0 1 5 (by decide) (by decide) with h187 | h187
              · linarith only [h182, h187, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h180, h182, h187, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h190 | h190
              · linarith only [h180, h182, h190, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h180, h182, h190, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h183, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h194 | h194
        · rcases p0_3 (m.d 3 5) (by simp) with h195 | h195
          · linarith only [h195, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h197 | h197
            · rcases m.htr 0 1 5 (by decide) (by decide) with h198 | h198
              · rcases m.htr 0 2 5 (by decide) (by decide) with h199 | h199
                · linarith only [h180, h198, h199, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h180, h197, h199, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h182, h197, h198, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
              · rcases m.htr 0 2 5 (by decide) (by decide) with h204 | h204
                · linarith only [h180, h203, h204, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h180, h204, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h182, h203, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h194, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h209 | h209
    · linarith only [h209, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h211 | h211
      · rcases p0_3 (m.d 2 5) (by simp) with h212 | h212
        · rcases p0_3 (m.d 3 5) (by simp) with h213 | h213
          · rcases p0_3 (m.d 4 5) (by simp) with h214 | h214
            · linarith only [h214, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
              · linarith only [h211, h216, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h209, h211, h216, hc01, hc15, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h219 | h219
            · linarith only [h219, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h221 | h221
              · linarith only [h209, h211, h221, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h209, h211, h221, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h212, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h225 | h225
        · rcases p0_3 (m.d 3 5) (by simp) with h226 | h226
          · rcases p0_3 (m.d 4 5) (by simp) with h227 | h227
            · linarith only [h227, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
              · rcases m.htr 0 2 5 (by decide) (by decide) with h230 | h230
                · linarith only [h209, h230, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h209, h230, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h211, h226, h229, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h234 | h234
            · linarith only [h234, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h236 | h236
              · rcases m.htr 0 2 5 (by decide) (by decide) with h237 | h237
                · linarith only [h209, h237, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h209, h237, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h211, h236, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h225, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h242 | h242
    · linarith only [h242, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h244 | h244
      · rcases p0_3 (m.d 2 5) (by simp) with h245 | h245
        · rcases p0_3 (m.d 3 5) (by simp) with h246 | h246
          · rcases p0_3 (m.d 4 5) (by simp) with h247 | h247
            · rcases m.htr 0 1 5 (by decide) (by decide) with h248 | h248
              · linarith only [h244, h248, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h244, h248, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h251 | h251
              · linarith only [h244, h251, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h244, h251, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h246, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h255 | h255
          · rcases p0_3 (m.d 4 5) (by simp) with h256 | h256
            · rcases m.htr 0 1 5 (by decide) (by decide) with h257 | h257
              · linarith only [h244, h257, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h244, h257, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h260 | h260
              · linarith only [h244, h260, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h244, h260, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h264 | h264
        · rcases p0_3 (m.d 3 5) (by simp) with h265 | h265
          · rcases p0_3 (m.d 4 5) (by simp) with h266 | h266
            · rcases m.htr 0 1 5 (by decide) (by decide) with h267 | h267
              · rcases m.htr 0 2 5 (by decide) (by decide) with h268 | h268
                · linarith only [h264, h267, h268, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h266, h268, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h244, h267, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h272 | h272
              · rcases m.htr 0 2 5 (by decide) (by decide) with h273 | h273
                · linarith only [h264, h272, h273, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h264, h273, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h244, h272, hlam]
          · linarith only [h265, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h278 | h278
          · rcases p0_3 (m.d 4 5) (by simp) with h279 | h279
            · rcases m.htr 0 1 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 0 2 5 (by decide) (by decide) with h281 | h281
                · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                  · linarith only [h282, hlam, p0_0]
                  · linarith only [h279, h282, hc03, hc45, hlam, hphi, ht34, p0_1]
                · linarith only [h264, h281, hlam]
              · linarith only [h244, h280, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h287 | h287
              · rcases m.htr 0 2 5 (by decide) (by decide) with h288 | h288
                · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                  · linarith only [h289, hlam, p0_0]
                  · linarith only [h289, hc03, hc35, hlam, hphi, p0_1]
                · linarith only [h264, h288, hlam]
              · linarith only [h244, h287, hlam]
          · linarith only [h278, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
    · linarith only [h295, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h297 | h297
      · linarith only [h297, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h299 | h299
        · rcases p0_3 (m.d 3 5) (by simp) with h300 | h300
          · rcases p0_3 (m.d 4 5) (by simp) with h301 | h301
            · rcases m.htr 0 1 5 (by decide) (by decide) with h302 | h302
              · linarith only [h295, h302, hlam]
              · linarith only [h301, h302, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h305 | h305
              · linarith only [h295, h305, hlam]
              · linarith only [h299, h305, hc01, hc25, hlam, hphi, ht12, p0_1]
          · linarith only [h300, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h309 | h309
          · rcases p0_3 (m.d 4 5) (by simp) with h310 | h310
            · rcases m.htr 0 1 5 (by decide) (by decide) with h311 | h311
              · linarith only [h295, h311, hlam]
              · linarith only [h310, h311, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h314 | h314
              · linarith only [h295, h314, hlam]
              · linarith only [h314, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h309, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h318 | h318
    · linarith only [h318, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h320 | h320
      · rcases p0_3 (m.d 2 5) (by simp) with h321 | h321
        · linarith only [h321, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h323 | h323
          · rcases p0_3 (m.d 4 5) (by simp) with h324 | h324
            · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
              · linarith only [h320, h325, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h318, h320, h325, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h328 | h328
              · linarith only [h318, h320, h328, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h318, h320, h328, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h323, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h332 | h332
        · linarith only [h332, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h334 | h334
          · rcases p0_3 (m.d 4 5) (by simp) with h335 | h335
            · rcases m.htr 0 1 5 (by decide) (by decide) with h336 | h336
              · rcases m.htr 0 2 5 (by decide) (by decide) with h337 | h337
                · linarith only [h318, h337, hlam]
                · linarith only [h335, h337, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h320, h335, h336, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h341 | h341
              · rcases m.htr 0 2 5 (by decide) (by decide) with h342 | h342
                · linarith only [h318, h342, hlam]
                · linarith only [h342, hc02, hc35, hlam, hphi, ht23, p0_1]
              · linarith only [h320, h341, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h334, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h348 | h348
    · linarith only [h348, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h350 | h350
      · rcases p0_3 (m.d 2 5) (by simp) with h351 | h351
        · rcases p0_3 (m.d 3 5) (by simp) with h352 | h352
          · rcases p0_3 (m.d 4 5) (by simp) with h353 | h353
            · linarith only [h353, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h355 | h355
              · linarith only [h350, h355, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h348, h350, h355, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h352, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h359 | h359
          · rcases p0_3 (m.d 4 5) (by simp) with h360 | h360
            · linarith only [h360, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
              · linarith only [h348, h350, h362, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h348, h350, h362, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h359, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h366 | h366
        · rcases p0_3 (m.d 3 5) (by simp) with h367 | h367
          · rcases p0_3 (m.d 4 5) (by simp) with h368 | h368
            · linarith only [h368, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h370 | h370
              · rcases m.htr 0 2 5 (by decide) (by decide) with h371 | h371
                · linarith only [h348, h366, h371, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h348, h366, h371, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h350, h370, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h367, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h376 | h376
          · rcases p0_3 (m.d 4 5) (by simp) with h377 | h377
            · linarith only [h377, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h379 | h379
              · rcases m.htr 0 2 5 (by decide) (by decide) with h380 | h380
                · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
                  · linarith only [h348, h381, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                  · linarith only [h348, h381, hc03, hc35, hlam, hphi, p0_1]
                · linarith only [h366, h380, hc02, hc35, hlam, hphi, ht23, p0_1]
              · linarith only [h350, h379, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h376, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h387 | h387
    · linarith only [h387, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h389 | h389
      · rcases p0_3 (m.d 2 5) (by simp) with h390 | h390
        · rcases p0_3 (m.d 3 5) (by simp) with h391 | h391
          · rcases p0_3 (m.d 4 5) (by simp) with h392 | h392
            · rcases m.htr 0 1 5 (by decide) (by decide) with h393 | h393
              · linarith only [h389, h393, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h389, h393, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h392, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h397 | h397
            · rcases m.htr 0 1 5 (by decide) (by decide) with h398 | h398
              · linarith only [h389, h398, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h389, h398, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h397, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h402 | h402
          · rcases p0_3 (m.d 4 5) (by simp) with h403 | h403
            · rcases m.htr 0 1 5 (by decide) (by decide) with h404 | h404
              · linarith only [h389, h404, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h389, h404, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h403, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h408 | h408
            · rcases m.htr 0 1 5 (by decide) (by decide) with h409 | h409
              · linarith only [h389, h409, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h389, h409, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h408, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h413 | h413
        · rcases p0_3 (m.d 3 5) (by simp) with h414 | h414
          · rcases p0_3 (m.d 4 5) (by simp) with h415 | h415
            · rcases m.htr 0 1 5 (by decide) (by decide) with h416 | h416
              · rcases m.htr 0 2 5 (by decide) (by decide) with h417 | h417
                · linarith only [h413, h416, h417, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h417, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h389, h416, hlam]
            · linarith only [h415, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h422 | h422
            · rcases m.htr 0 1 5 (by decide) (by decide) with h423 | h423
              · rcases m.htr 0 2 5 (by decide) (by decide) with h424 | h424
                · linarith only [h413, h423, h424, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h424, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h389, h423, hlam]
            · linarith only [h422, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h429 | h429
          · rcases p0_3 (m.d 4 5) (by simp) with h430 | h430
            · rcases m.htr 0 1 5 (by decide) (by decide) with h431 | h431
              · rcases m.htr 0 2 5 (by decide) (by decide) with h432 | h432
                · rcases m.htr 0 3 5 (by decide) (by decide) with h433 | h433
                  · linarith only [h429, h431, h433, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                  · linarith only [h433, hc03, hc45, hlam, hphi, ht34, p0_1]
                · linarith only [h413, h432, hlam]
              · linarith only [h389, h431, hlam]
            · linarith only [h430, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h439 | h439
            · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
              · rcases m.htr 0 2 5 (by decide) (by decide) with h441 | h441
                · rcases m.htr 0 3 5 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h443 | h443
                    · linarith only [h443, hlam, p0_0]
                    · linarith only [h443, hc04, hc45, hlam, hphi, p0_1]
                  · linarith only [h429, h442, hlam]
                · linarith only [h413, h441, hlam]
              · linarith only [h389, h440, hlam]
            · linarith only [h439, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h450 | h450
    · linarith only [h450, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h452 | h452
      · linarith only [h452, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h454 | h454
        · rcases p0_3 (m.d 3 5) (by simp) with h455 | h455
          · rcases p0_3 (m.d 4 5) (by simp) with h456 | h456
            · rcases m.htr 0 1 5 (by decide) (by decide) with h457 | h457
              · linarith only [h450, h457, hlam]
              · linarith only [h454, h457, hc01, hc25, hlam, hphi, ht12, p0_1]
            · linarith only [h456, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h461 | h461
            · rcases m.htr 0 1 5 (by decide) (by decide) with h462 | h462
              · linarith only [h450, h462, hlam]
              · linarith only [h462, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h461, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h466 | h466
          · rcases p0_3 (m.d 4 5) (by simp) with h467 | h467
            · rcases m.htr 0 1 5 (by decide) (by decide) with h468 | h468
              · linarith only [h450, h468, hlam]
              · linarith only [h468, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h467, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h472 | h472
            · rcases m.htr 0 1 5 (by decide) (by decide) with h473 | h473
              · linarith only [h450, h473, hlam]
              · linarith only [h473, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h472, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h477 | h477
    · linarith only [h477, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h479 | h479
      · rcases p0_3 (m.d 2 5) (by simp) with h480 | h480
        · linarith only [h480, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h482 | h482
          · rcases p0_3 (m.d 4 5) (by simp) with h483 | h483
            · rcases m.htr 0 1 5 (by decide) (by decide) with h484 | h484
              · linarith only [h479, h484, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h477, h479, h484, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h483, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h488 | h488
            · rcases m.htr 0 1 5 (by decide) (by decide) with h489 | h489
              · linarith only [h477, h479, h489, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h477, h479, h489, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h493 | h493
        · linarith only [h493, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h495 | h495
          · rcases p0_3 (m.d 4 5) (by simp) with h496 | h496
            · rcases m.htr 0 1 5 (by decide) (by decide) with h497 | h497
              · rcases m.htr 0 2 5 (by decide) (by decide) with h498 | h498
                · linarith only [h477, h498, hlam]
                · linarith only [h498, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h479, h497, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h496, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h503 | h503
            · rcases m.htr 0 1 5 (by decide) (by decide) with h504 | h504
              · rcases m.htr 0 2 5 (by decide) (by decide) with h505 | h505
                · linarith only [h477, h505, hlam]
                · linarith only [h505, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h479, h504, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h503, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h510 | h510
    · linarith only [h510, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h512 | h512
      · rcases p0_3 (m.d 2 5) (by simp) with h513 | h513
        · rcases p0_3 (m.d 3 5) (by simp) with h514 | h514
          · linarith only [h514, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h516 | h516
            · rcases m.htr 0 1 5 (by decide) (by decide) with h517 | h517
              · linarith only [h512, h517, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h510, h512, h517, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h516, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h521 | h521
          · linarith only [h521, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h523 | h523
            · rcases m.htr 0 1 5 (by decide) (by decide) with h524 | h524
              · linarith only [h510, h512, h524, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h510, h512, h524, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h523, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h528 | h528
        · rcases p0_3 (m.d 3 5) (by simp) with h529 | h529
          · linarith only [h529, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h531 | h531
            · rcases m.htr 0 1 5 (by decide) (by decide) with h532 | h532
              · rcases m.htr 0 2 5 (by decide) (by decide) with h533 | h533
                · linarith only [h510, h528, h532, h533, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h510, h533, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h512, h532, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h531, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h538 | h538
          · linarith only [h538, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h540 | h540
            · rcases m.htr 0 1 5 (by decide) (by decide) with h541 | h541
              · rcases m.htr 0 2 5 (by decide) (by decide) with h542 | h542
                · rcases m.htr 0 3 5 (by decide) (by decide) with h543 | h543
                  · linarith only [h510, h543, hlam]
                  · linarith only [h543, hc03, hc45, hlam, hphi, ht34, p0_1]
                · linarith only [h528, h542, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h512, h541, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h540, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_M_LI_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
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
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h10, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h0, h10, h13, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h14, hc14, hlam, hphi, ht45, u5elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                                · linarith only [h0, h10, h20, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                                  · linarith only [h0, h10, h13, h22, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h22, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h19, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h12, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h10, h28, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                          · linarith only [h0, h10, h30, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h30, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                            · linarith only [h1, h40, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                                · linarith only [h35, h37, h43, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                                  · linarith only [h0, h38, h43, h45, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h35, h45, h7, hc23, hc34, hlam, hphi]
                              · linarith only [h42, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h39, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h37, h38, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h37, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h35, h36, h7, hc35, hlam, hphi, u5elo4]
                  · linarith only [h35, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h56 | h56
            · rcases m.htr 0 2 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 0 3 5 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                      · linarith only [h0, h4, h56, h61, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                                    · linarith only [h0, h63, h69, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h69, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h4, h68, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h4, h67, hc02, hlam, hphi, ht23, ht34, u4elo3]
                              · linarith only [h66, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h61, h63, h65, hc24, hlam, hphi, u4elo3]
                          · linarith only [h63, h64, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h4, h56, h63, hc12, hc23, hlam, hphi]
                    · linarith only [h60, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h4, h59, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h4, h56, h58, hc24, hlam, hphi, u4elo3]
              · linarith only [h56, h57, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h82 | h82
              · rcases m.htr 0 3 4 (by decide) (by decide) with h83 | h83
                · rcases m.htr 0 3 5 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                      · linarith only [h0, h56, h86, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                        · linarith only [h0, h56, h88, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                                      · linarith only [h1, h91, h96, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h96, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h56, h90, h92, h94, h95, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h56, h93, h94, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h1, h91, h93, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h92, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h1, h83, h86, h90, h91, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h90, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h85, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h84, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                      · linarith only [h0, h109, h4, h82, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h111 | h111
                        · linarith only [h0, h111, h4, h83, hc24, hlam, hphi, u4elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                            · linarith only [h1, h114, h83, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h120 | h120
                                      · rcases h0bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h0, h113, h118, h120, hc45, hlam, hphi, ht0b, ht5b, p121_1, u0elo0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h1, h109, h113, h118, h120, hc45, hlam, hphi, ht0b, ht5b, p121_1, u0elo0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h1, h109, h113, h118, h120, h83, hc45, hlam, hphi, ht0b, ht5b, p121_1, u0elo0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          rcases p121_3 (m.d 0 1) (by simp) with h126 | h126
                                          · rcases p121_3 (m.d 0 2) (by simp) with h127 | h127
                                            · linarith only [h0, h127, hlam]
                                            · linarith only [h127, h82, hlam]
                                          · linarith only [h126, h3, hlam]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h0, hlam, p121_1]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h4, hlam, p121_1]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h56, hlam, p121_1]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h117, h4, h83, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p121_1, u4elo2]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h1, hlam, p121_1]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h117, h83, hc02, hlam, hphi, ht23, ht34, p121_1, u4elo2]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h83, hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h117, h83, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p121_1, u4elo2]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h2, hlam, p121_1]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [hc02, hlam, hphi, ht23, ht34, p121_1, u4elo0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h117, h83, hc03, hlam, hphi, ht34, p121_1, u4elo2]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          rcases p121_3 (m.d 0 1) (by simp) with h145 | h145
                                          · rcases p121_3 (m.d 0 2) (by simp) with h146 | h146
                                            · linarith only [h146, h56, hlam]
                                            · linarith only [h146, h82, hlam]
                                          · linarith only [h145, h3, hlam]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h3, hlam, p121_1]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h82, hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h107, hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [h108, hlam, p121_0]
                                        · have p121_0 := h121c.1
                                          have p121_1 := h121c.2.1
                                          have p121_2 := h121c.2.2.1
                                          have p121_3 := h121c.2.2.2
                                          linarith only [hlam, p121_0]
                                      · linarith only [h120, h83, hc04, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h116, h117, h119, h2, h4, h83, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h113, h117, h118, h4, h83, hc23, hc25, hlam, hphi, ht34, u4elo2, u5elo3]
                                · linarith only [h0, h113, h117, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                              · linarith only [h116, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h113, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h108, h4, h82, h83, hc25, hlam, hphi, u5elo4]
                  · linarith only [h107, h4, h82, hc25, hlam, hphi, u5elo3]
              · linarith only [h82, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h166 | h166
      · rcases m.htr 0 1 5 (by decide) (by decide) with h167 | h167
        · rcases m.htr 0 2 3 (by decide) (by decide) with h168 | h168
          · linarith only [h0, h1, h168, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h170 | h170
            · rcases m.htr 0 2 5 (by decide) (by decide) with h171 | h171
              · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
                · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h174 | h174
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
                      · linarith only [h0, h168, h175, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                                    · linarith only [h0, h1, h175, h177, h183, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h181, h183, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h1, h175, h177, h181, h182, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h0, h1, h175, h177, h181, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h180, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h1, h177, h179, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h177, h178, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h1, h170, h175, h177, hc12, hc23, hlam, hphi]
                    · linarith only [h174, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h173, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h172, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h171, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h196 | h196
              · rcases m.htr 0 3 4 (by decide) (by decide) with h197 | h197
                · rcases m.htr 0 3 5 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
                      · linarith only [h0, h170, h200, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                        · linarith only [h0, h170, h202, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h206 | h206
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                                      · rcases h0bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h0, h204, h208, h210, hc45, hlam, hphi, ht0b, ht5b, p211_1, u0elo0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h1, hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h0, h1, h170, h200, h204, h208, h210, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p211_1]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          rcases p211_3 (m.d 0 1) (by simp) with h216 | h216
                                          · rcases p211_3 (m.d 0 2) (by simp) with h217 | h217
                                            · linarith only [h0, h217, hlam]
                                            · linarith only [h196, h217, hlam]
                                          · linarith only [h167, h216, hlam]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h0, hlam, p211_1]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h168, hlam, p211_1]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h170, hlam, p211_1]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h170, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p211_1, u4elo2]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p211_1, u0elo2]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h0, h204, h208, h210, hc45, hlam, hphi, ht0b, ht5b, p211_1, u0elo2]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h0, h170, h204, h208, h210, hc45, hlam, hphi, ht0b, ht5b, p211_1, u0elo2]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          rcases p211_3 (m.d 0 1) (by simp) with h230 | h230
                                          · linarith only [h1, h230, hlam]
                                          · linarith only [h167, h230, hlam]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h166, hlam, p211_1]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h0, h204, h208, h210, hc45, hlam, hphi, ht0b, ht5b, p211_1, u0elo3]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h197, hlam, p211_1]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          rcases p211_3 (m.d 0 1) (by simp) with h237 | h237
                                          · rcases p211_3 (m.d 0 2) (by simp) with h238 | h238
                                            · linarith only [h170, h238, hlam]
                                            · linarith only [h196, h238, hlam]
                                          · linarith only [h167, h237, hlam]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h167, hlam, p211_1]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h196, hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h198, hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [h199, hlam, p211_0]
                                        · have p211_0 := h211c.1
                                          have p211_1 := h211c.2.1
                                          have p211_2 := h211c.2.2.1
                                          have p211_3 := h211c.2.2.2
                                          linarith only [hlam, p211_0]
                                      · linarith only [h210, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h167, h170, h204, h206, h209, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                                  · linarith only [h1, h166, h200, h202, h204, h208, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h166, h200, h202, h204, h207, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h202, h204, h206, hc25, hlam, hphi, u5elo4]
                            · linarith only [h1, h166, h202, h204, h205, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h204, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h199, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h198, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h197, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h196, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h167, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h166, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h260 | h260
    · rcases m.htr 0 1 4 (by decide) (by decide) with h261 | h261
      · rcases m.htr 0 1 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 2 3 (by decide) (by decide) with h263 | h263
          · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
            · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
              · rcases m.htr 0 3 4 (by decide) (by decide) with h266 | h266
                · rcases m.htr 0 3 5 (by decide) (by decide) with h267 | h267
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                                      · linarith only [h260, h269, h274, h277, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h277, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h260, h272, h273, h276, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h267, h275, hc23, hlam, hphi, ht34, ht45, u5elo0]
                                · linarith only [h0, h260, h272, h274, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h273, hc14, hlam, hphi, ht45, u5elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                                · linarith only [h269, h272, h285, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h287 | h287
                                  · linarith only [h0, h260, h266, h269, h272, h287, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h287, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h284, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h271, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h260, h269, h270, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h263, h269, hlam]
                    · linarith only [h268, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h266, h267, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
                            · linarith only [h260, h266, h301, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
                                · linarith only [h260, h266, h298, h304, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h306 | h306
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h307 | h307
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h308 | h308
                                      · rcases h0bigk with h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h0, hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h0, h260, h298, h306, h308, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p309_1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h0, h260, h266, h298, h306, h308, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p309_1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          rcases p309_3 (m.d 0 1) (by simp) with h314 | h314
                                          · rcases p309_3 (m.d 0 2) (by simp) with h315 | h315
                                            · rcases p309_3 (m.d 0 3) (by simp) with h316 | h316
                                              · linarith only [h260, h316, hlam]
                                              · linarith only [h296, h316, hlam]
                                            · linarith only [h265, h315, hlam]
                                          · linarith only [h262, h314, hlam]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h260, h298, h306, h308, hc45, hlam, hphi, ht0b, ht5b, p309_1, u0elo1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h260, h298, h306, h308, hc45, hlam, hphi, ht0b, ht5b, p309_1, u0elo1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h260, h266, h298, h306, h308, hc45, hlam, hphi, ht0b, ht5b, p309_1, u0elo1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          rcases p309_3 (m.d 0 1) (by simp) with h325 | h325
                                          · linarith only [h0, h325, hlam]
                                          · linarith only [h262, h325, hlam]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h260, hlam, p309_1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h263, hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h266, hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h262, h266, h300, h306, h308, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p309_1, u4elo3]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h261, hlam, p309_1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h264, hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [hc03, hlam, hphi, ht34, p309_1, u4elo0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          rcases p309_3 (m.d 0 1) (by simp) with h337 | h337
                                          · rcases p309_3 (m.d 0 2) (by simp) with h338 | h338
                                            · rcases p309_3 (m.d 0 3) (by simp) with h339 | h339
                                              · linarith only [h266, h339, hlam]
                                              · linarith only [h296, h339, hlam]
                                            · linarith only [h265, h338, hlam]
                                          · linarith only [h262, h337, hlam]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h262, hlam, p309_1]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h265, hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h296, hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [h297, hlam, p309_0]
                                        · have p309_0 := h309c.1
                                          have p309_1 := h309c.2.1
                                          have p309_2 := h309c.2.2.1
                                          have p309_3 := h309c.2.2.2
                                          linarith only [hlam, p309_0]
                                      · linarith only [h266, h308, hc04, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h304, h307, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h306, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h303, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h300, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h299, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h263, h298, hlam]
                    · linarith only [h266, h296, h297, hc35, hlam, hphi, u5elo4]
                  · linarith only [h296, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h265, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h260, h264, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h260, h263, hlam]
        · linarith only [h260, h262, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · linarith only [h260, h261, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h363 | h363
      · rcases m.htr 0 1 5 (by decide) (by decide) with h364 | h364
        · rcases m.htr 0 2 3 (by decide) (by decide) with h365 | h365
          · rcases m.htr 0 2 4 (by decide) (by decide) with h366 | h366
            · rcases m.htr 0 2 5 (by decide) (by decide) with h367 | h367
              · rcases m.htr 0 3 4 (by decide) (by decide) with h368 | h368
                · rcases m.htr 0 3 5 (by decide) (by decide) with h369 | h369
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h373 | h373
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                                      · linarith only [h365, h376, h379, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h363, h372, h378, h379, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · linarith only [h378, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h377, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h384 | h384
                                  · linarith only [h365, h368, h376, h384, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h384, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h375, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h260, h374, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h373, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h363, h370, h372, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                      · linarith only [h0, h365, h371, hlam]
                    · linarith only [h370, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h369, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h260, h363, h368, hc14, hlam, hphi, u4elo3]
              · linarith only [h367, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h260, h363, h365, h366, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h397 | h397
            · rcases m.htr 0 2 5 (by decide) (by decide) with h398 | h398
              · rcases m.htr 0 3 4 (by decide) (by decide) with h399 | h399
                · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h403 | h403
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
                              · linarith only [h0, h363, h365, h402, h406, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h406, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h365, h402, h405, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h363, h365, h402, h403, h404, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h363, h365, h402, h403, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h413 | h413
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h415 | h415
                              · linarith only [h0, h363, h402, h415, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h415, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h260, h363, h412, h414, hc24, hlam, hphi, u4elo3]
                          · linarith only [h0, h363, h412, h413, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h363, h412, hc14, hlam, hphi, u4elo2]
                    · linarith only [h401, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h363, h365, h400, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h0, h363, h365, h399, hc14, hlam, hphi, u4elo3]
              · linarith only [h0, h363, h398, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h363, h397, hc14, hlam, hphi, u4elo2]
        · linarith only [h363, h364, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h427 | h427
        · rcases m.htr 0 2 3 (by decide) (by decide) with h428 | h428
          · rcases m.htr 0 2 4 (by decide) (by decide) with h429 | h429
            · rcases m.htr 0 2 5 (by decide) (by decide) with h430 | h430
              · rcases m.htr 0 3 4 (by decide) (by decide) with h431 | h431
                · rcases m.htr 0 3 5 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h435 | h435
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h436 | h436
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h437 | h437
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h438 | h438
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h439 | h439
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h440 | h440
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h441 | h441
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h442 | h442
                                      · linarith only [h428, h439, h442, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h442, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h363, h427, h438, h441, hc24, hlam, hphi, u4elo1]
                                  · linarith only [h363, h427, h436, h440, hc23, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                                  · linarith only [h431, h439, h447, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h447, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h363, h427, h436, h438, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h260, h431, h437, hlam]
                          · linarith only [h0, h436, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h260, h427, h429, h434, h435, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h428, h434, hlam]
                    · linarith only [h363, h427, h433, hc15, hlam, hphi, u5elo4]
                  · linarith only [h431, h432, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                                · linarith only [h260, h427, h428, h431, h461, h464, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
                                      · rcases h0bigk with h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h0, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h260, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h363, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h260, h431, h462, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p469_1, u4elo1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h427, hc15, hlam, hphi, ht0b, ht5b, p469_1, u0elo1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h260, h427, h461, h466, h468, hc45, hlam, hphi, ht0b, ht5b, p469_1, u0elo1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h260, h427, h431, h461, h466, h468, hc45, hlam, hphi, ht0b, ht5b, p469_1, u0elo1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          rcases p469_3 (m.d 0 1) (by simp) with h479 | h479
                                          · linarith only [h0, h479, hlam]
                                          · linarith only [h427, h479, hlam]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h427, h431, h461, h462, h466, h468, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p469_1, u4elo1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h428, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h431, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h427, h431, h461, h462, h466, h468, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p469_1, u4elo1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h427, h461, h466, h468, hc45, hlam, hphi, ht0b, ht5b, p469_1, u0elo3]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h429, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h431, h462, hc03, hlam, hphi, ht34, p469_1, u4elo1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          rcases p469_3 (m.d 0 1) (by simp) with h491 | h491
                                          · linarith only [h363, h491, hlam]
                                          · linarith only [h427, h491, hlam]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h427, hlam, p469_1]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h430, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h457, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [h458, hlam, p469_0]
                                        · have p469_0 := h469c.1
                                          have p469_1 := h469c.2.1
                                          have p469_2 := h469c.2.2.1
                                          have p469_3 := h469c.2.2.2
                                          linarith only [hlam, p469_0]
                                      · linarith only [h431, h468, hc04, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h260, h427, h431, h462, h463, h467, hc24, hlam, hphi, u4elo1]
                                  · linarith only [h260, h427, h431, h462, h466, hc15, hc23, hlam, hphi, ht34, u4elo1, u5elo3]
                              · linarith only [h260, h427, h431, h461, h462, h463, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h260, h427, h461, h462, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h461, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h260, h459, h460, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h427, h428, h459, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h260, h427, h431, h458, hc15, hlam, hphi, u5elo4]
                  · linarith only [h260, h427, h457, hc15, hlam, hphi, u5elo3]
              · linarith only [h430, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h428, h429, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h511 | h511
            · rcases m.htr 0 2 5 (by decide) (by decide) with h512 | h512
              · rcases m.htr 0 3 4 (by decide) (by decide) with h513 | h513
                · rcases m.htr 0 3 5 (by decide) (by decide) with h514 | h514
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h515 | h515
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h517 | h517
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h518 | h518
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h520 | h520
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h521 | h521
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h522 | h522
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                                    · linarith only [h428, h511, h516, h523, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h363, h427, h518, h522, h523, hc24, hc35, hlam, hphi, u4elo1, u5elo4]
                                  · linarith only [h363, h427, h428, h518, h522, hc02, hc25, hlam, hphi, ht23, ht34, u4elo1, u5elo3]
                                · linarith only [h363, h427, h428, h511, h518, h521, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                              · linarith only [h363, h427, h518, h520, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h428, h513, h516, h519, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h428, h516, h518, hc03, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h428, h511, h516, h517, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h533 | h533
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h536 | h536
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h537 | h537
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h538 | h538
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h539 | h539
                                      · rcases h0bigk with h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h0, hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h260, hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h363, hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h363, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p540_1, u4elo1]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h427, h428, hc15, hlam, hphi, ht0b, ht5b, p540_1, u0elo2]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h428, hlam, p540_1]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h0, h363, h427, h516, h533, h537, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p540_1]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          rcases p540_3 (m.d 0 1) (by simp) with h550 | h550
                                          · linarith only [h0, h550, hlam]
                                          · linarith only [h427, h550, hlam]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h427, h533, h537, h539, hc45, hlam, hphi, ht0b, ht5b, p540_1, u0elo2]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h0, h427, h533, h537, h539, hc45, hlam, hphi, ht0b, ht5b, p540_1, u0elo2]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h363, h427, h533, h537, h539, hc45, hlam, hphi, ht0b, ht5b, p540_1, u0elo2]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          rcases p540_3 (m.d 0 1) (by simp) with h557 | h557
                                          · linarith only [h260, h557, hlam]
                                          · linarith only [h427, h557, hlam]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h427, h533, h537, h539, hc45, hlam, hphi, ht0b, ht5b, p540_1, u0elo3]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h511, hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h513, hlam, p540_1]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          rcases p540_3 (m.d 0 1) (by simp) with h564 | h564
                                          · linarith only [h363, h564, hlam]
                                          · linarith only [h427, h564, hlam]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h427, hlam, p540_1]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h512, hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h514, hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [h515, hlam, p540_0]
                                        · have p540_0 := h540c.1
                                          have p540_1 := h540c.2.1
                                          have p540_2 := h540c.2.2.1
                                          have p540_3 := h540c.2.2.2
                                          linarith only [hlam, p540_0]
                                      · linarith only [h539, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h363, h427, h535, h538, hc24, hlam, hphi, u4elo1]
                                  · linarith only [h0, h516, h537, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h363, h427, h516, h532, h533, h536, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h363, h427, h533, h535, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h260, h427, h511, h513, h533, h534, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h0, h533, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h427, h532, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h363, h427, h515, hc15, hlam, hphi, u5elo4]
                  · linarith only [h363, h427, h428, h511, h514, hc15, hlam, hphi, u5elo3]
                · linarith only [h428, h511, h513, hc24, hlam, hphi, u4elo3]
              · linarith only [h363, h427, h511, h512, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h584 | h584
              · rcases m.htr 0 3 4 (by decide) (by decide) with h585 | h585
                · rcases m.htr 0 3 5 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h587 | h587
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h590 | h590
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h591 | h591
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h592 | h592
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h594 | h594
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h595 | h595
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h596 | h596
                                      · rcases h0bigk with h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h0, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h260, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h363, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h0, h511, h589, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p597_1, u4elo1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h511, h589, hc01, hlam, hphi, ht12, ht23, ht34, p597_1, u4elo1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h428, hlam, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h511, hlam, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h427, h511, h589, h590, h594, h596, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p597_1, u4elo1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h427, h590, h594, h596, hc45, hlam, hphi, ht0b, ht5b, p597_1, u0elo2]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h0, h427, h590, h594, h596, hc45, hlam, hphi, ht0b, ht5b, p597_1, u0elo2]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h0, h427, h428, h511, h588, h590, h594, h596, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          rcases p597_3 (m.d 0 1) (by simp) with h612 | h612
                                          · linarith only [h260, h612, hlam]
                                          · linarith only [h427, h612, hlam]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h427, h590, h594, h596, hc45, hlam, hphi, ht0b, ht5b, p597_1, u0elo3]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h0, h427, h511, h589, h590, h594, h596, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p597_1, u4elo1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h585, hlam, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          rcases p597_3 (m.d 0 1) (by simp) with h619 | h619
                                          · linarith only [h363, h619, hlam]
                                          · linarith only [h427, h619, hlam]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h427, hlam, p597_1]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h584, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h586, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [h587, hlam, p597_0]
                                        · have p597_0 := h597c.1
                                          have p597_1 := h597c.2.1
                                          have p597_2 := h597c.2.2.1
                                          have p597_3 := h597c.2.2.2
                                          linarith only [hlam, p597_0]
                                      · linarith only [h596, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h427, h511, h592, h595, hlam]
                                  · linarith only [h428, h594, hc03, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h0, h427, h428, h590, h593, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                              · linarith only [h0, h427, h511, h589, h590, h592, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h260, h427, h585, h590, h591, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h0, h427, h511, h589, h590, hc12, hc15, hlam, hphi, ht23, ht34, u4elo1, u5elo2]
                        · linarith only [h0, h427, h428, h588, h589, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
                        · linarith only [h0, h427, h511, h588, h635, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h427, h635, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h587, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h427, h511, h586, hc03, hc15, hlam, hphi, ht34, u4elo2, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h640 | h640
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h641 | h641
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h643 | h643
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h644 | h644
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h645 | h645
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h646 | h646
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h647 | h647
                                · linarith only [h0, h427, h428, h585, h642, h644, h647, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h427, h428, h644, h645, h647, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                              · linarith only [h646, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h427, h428, h642, h644, h645, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h644, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h642, h643, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
                        · linarith only [h0, h427, h511, h642, h654, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h427, h654, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h641, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h427, h428, h640, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h427, h584, hc15, hlam, hphi, u5elo2]
        · linarith only [h427, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT4_M_LI_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h5ehi := hb5.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h2, h7, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                · linarith only [h6, h7, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h2, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h11, h6, h7, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14 | h14
              · linarith only [h14, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
                · linarith only [h1, h16, h2, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, h2, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h1, h16, h20, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi0]
                    · linarith only [h1, h2, h20, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
            · linarith only [h23, h4, h5, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
              · linarith only [h25, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                · linarith only [h1, h27, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h2, h23, h29, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h1, h2, h27, h31, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h1, h2, h31, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h34 | h34
          · rcases m.htr 0 3 4 (by decide) (by decide) with h35 | h35
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h36, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
                · linarith only [h38, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                  · linarith only [h0, h2, h40, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h35, h36, h40, hc13, hc35, hlam, hphi]
            · linarith only [h34, h35, h4, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h44 | h44
            · rcases m.htr 0 3 5 (by decide) (by decide) with h45 | h45
              · linarith only [h45, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
                · linarith only [h44, h45, h47, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                  · linarith only [h0, h2, h49, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h44, h45, h49, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
              · linarith only [h52, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h54 | h54
                · linarith only [h1, h2, h54, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h0, h2, h56, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h1, h2, h4, h44, h54, h58, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h2, h58, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h61 | h61
      · linarith only [h61, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h63 | h63
        · rcases m.htr 0 2 4 (by decide) (by decide) with h64 | h64
          · rcases m.htr 0 3 4 (by decide) (by decide) with h65 | h65
            · linarith only [h0, h1, h65, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h67 | h67
              · linarith only [h65, h67, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h69 | h69
                · linarith only [h64, h69, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h0, h1, h69, h71, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                    · linarith only [h0, h1, h69, h71, h73, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h1, h73, hc13, hc45, hlam, hphi, ht34]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
            · linarith only [h0, h1, h76, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h78 | h78
              · linarith only [h0, h78, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
                · linarith only [h80, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h1, h80, h82, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                    · linarith only [h0, h1, h80, h82, h84, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h1, h84, hc13, hc45, hlam, hphi, ht34]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
          · linarith only [h0, h1, h63, h87, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h89 | h89
            · linarith only [h0, h1, h89, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
              · linarith only [h0, h91, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h93 | h93
                · linarith only [h93, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                  · linarith only [h0, h1, h93, h95, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                    · linarith only [h0, h1, h93, h95, h97, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h1, h97, hc13, hc45, hlam, hphi, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h100 | h100
    · rcases m.htr 0 1 5 (by decide) (by decide) with h101 | h101
      · linarith only [h101, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h103 | h103
        · rcases m.htr 0 2 4 (by decide) (by decide) with h104 | h104
          · rcases m.htr 0 3 4 (by decide) (by decide) with h105 | h105
            · rcases m.htr 0 3 5 (by decide) (by decide) with h106 | h106
              · linarith only [h103, h106, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                · linarith only [h108, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                    · linarith only [h0, h100, h106, h108, h111, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · linarith only [h100, h101, h110, h111, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h0, h100, h110, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
            · linarith only [h0, h100, h105, hlam]
          · linarith only [h0, h100, h103, h104, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h117 | h117
          · rcases m.htr 0 3 4 (by decide) (by decide) with h118 | h118
            · rcases m.htr 0 3 5 (by decide) (by decide) with h119 | h119
              · linarith only [h119, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                · linarith only [h100, h121, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                    · linarith only [h0, h100, h119, h121, h124, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · linarith only [h100, h101, h123, h124, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h0, h100, h123, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
            · linarith only [h0, h100, h118, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h129 | h129
            · rcases m.htr 0 3 5 (by decide) (by decide) with h130 | h130
              · linarith only [h130, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                · linarith only [h0, h100, h130, h132, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                    · linarith only [h0, h100, h130, h132, h135, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · linarith only [h100, h101, h134, h135, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h0, h100, h134, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
            · linarith only [h0, h100, h129, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h140 | h140
      · linarith only [h140, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h142 | h142
        · rcases m.htr 0 2 4 (by decide) (by decide) with h143 | h143
          · rcases m.htr 0 3 4 (by decide) (by decide) with h144 | h144
            · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
              · linarith only [h142, h145, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
                · linarith only [h144, h145, h147, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                      · linarith only [h144, h145, h147, h151, hlam]
                      · linarith only [h144, h145, h149, h150, h151, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h154 | h154
                      · linarith only [h100, h144, h150, h154, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h144, h145, h154, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h144, h145, h149, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h158 | h158
              · linarith only [h144, h158, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
                · linarith only [h160, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                      · linarith only [h160, h162, h164, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h144, h162, h163, h164, hc01, hc13, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                      · linarith only [h162, h163, h167, hlam]
                      · rcases h0bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h0, h144, hc02, hc34, hlam, hphi, ht23, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h0, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h100, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h140, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 1) (by simp) with h175 | h175
                          · linarith only [h175, hlam, p169_0]
                          · rcases p169_3 (m.d 0 2) (by simp) with h177 | h177
                            · rcases p169_3 (m.d 0 3) (by simp) with h178 | h178
                              · linarith only [h142, h178, hlam]
                              · linarith only [h0, h178, hlam]
                            · linarith only [h177, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 1) (by simp) with h183 | h183
                          · linarith only [h0, h183, hlam, p169_1]
                          · rcases p169_3 (m.d 0 2) (by simp) with h185 | h185
                            · rcases p169_3 (m.d 0 3) (by simp) with h186 | h186
                              · linarith only [h142, h186, hlam]
                              · rcases p169_3 (m.d 0 4) (by simp) with h188 | h188
                                · linarith only [h143, h188, hlam]
                                · linarith only [h144, h188, hlam]
                            · linarith only [h142, h185, hlam]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h143, hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo1, u4ehi2]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht5b, p169_1, u0elo1, u5ehi0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h144, h162, hc01, hc14, hlam, hphi, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h142, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h144, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h158, hlam, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h160, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h143, hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h160, hc03, hc45, hlam, hphi, ht34, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h160, hlam, p169_1]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 1) (by simp) with h204 | h204
                          · linarith only [h140, h204, hlam]
                          · rcases p169_3 (m.d 0 2) (by simp) with h206 | h206
                            · rcases p169_3 (m.d 0 3) (by simp) with h207 | h207
                              · linarith only [h158, h207, hlam]
                              · linarith only [h0, h207, hlam]
                            · linarith only [h142, h206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1, u0elo4]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [h143, hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo4, u4ehi2]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          rcases p169_3 (m.d 0 1) (by simp) with h212 | h212
                          · linarith only [h140, h212, hlam]
                          · rcases p169_3 (m.d 0 2) (by simp) with h214 | h214
                            · rcases p169_3 (m.d 0 3) (by simp) with h215 | h215
                              · linarith only [h158, h215, hlam]
                              · rcases p169_3 (m.d 0 4) (by simp) with h217 | h217
                                · linarith only [h160, h217, hlam]
                                · linarith only [h144, h217, hlam]
                            · linarith only [h142, h214, hlam]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo4, u4ehi0]
                        · have p169_0 := h169c.1
                          have p169_1 := h169c.2.1
                          have p169_2 := h169c.2.2.1
                          have p169_3 := h169c.2.2.2
                          linarith only [hlam, p169_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h224 | h224
                      · rcases h0bigk with h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h100, h162, hc02, hc34, hlam, hphi, ht23, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h0, hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h100, hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h140, hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          rcases p225_3 (m.d 0 1) (by simp) with h231 | h231
                          · linarith only [h231, hlam, p225_0]
                          · rcases p225_3 (m.d 0 2) (by simp) with h233 | h233
                            · rcases p225_3 (m.d 0 3) (by simp) with h234 | h234
                              · linarith only [h142, h234, hlam]
                              · linarith only [h0, h234, hlam]
                            · linarith only [h233, hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          rcases p225_3 (m.d 0 1) (by simp) with h239 | h239
                          · linarith only [h0, h239, hlam, p225_1]
                          · rcases p225_3 (m.d 0 2) (by simp) with h241 | h241
                            · rcases p225_3 (m.d 0 3) (by simp) with h242 | h242
                              · linarith only [h142, h242, hlam]
                              · rcases p225_3 (m.d 0 4) (by simp) with h244 | h244
                                · linarith only [h143, h244, hlam]
                                · linarith only [h144, h244, hlam]
                            · linarith only [h142, h241, hlam]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht45, ht5b, p225_1, u0elo1, u4ehi0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht5b, p225_1, u0elo1, u5ehi0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h144, hc01, hc34, hlam, hphi, ht12, ht23, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h142, hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h144, hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h158, hlam, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h160, h162, h223, hc01, hc34, hlam, hphi, ht12, ht23, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h143, hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h160, h223, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [hlam, p225_0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h160, hlam, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h160, h162, h223, hc01, hc34, hlam, hphi, ht12, ht23, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h160, h162, h223, hc02, hc34, hlam, hphi, ht23, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h0, h160, h162, h223, hc01, hc34, hlam, hphi, ht12, ht23, p225_1]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [h160, h162, h223, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p225_1, u4ehi0]
                        · have p225_0 := h225c.1
                          have p225_1 := h225c.2.1
                          have p225_2 := h225c.2.2.1
                          have p225_3 := h225c.2.2.2
                          linarith only [hlam, p225_0]
                      · linarith only [h162, h223, h224, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h162, h223, h266, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h162, h266, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h269 | h269
            · linarith only [h142, h143, h269, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h271 | h271
              · linarith only [h142, h143, h271, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
                · linarith only [h273, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                      · linarith only [h142, h143, h273, h275, h277, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h269, h275, h276, h277, hc01, hc13, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                      · linarith only [h100, h276, h280, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h0bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h142, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1, u0elo0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h0, hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h100, hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h140, hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h143, h269, h275, h276, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h143, h269, h275, h276, hc03, hc45, hlam, hphi, ht34, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h143, hlam, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h143, h269, h275, h276, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p282_1, u5ehi0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h142, h143, h269, h275, h276, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h142, hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h269, hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h271, hlam, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h269, h275, h276, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h269, h275, h276, hc02, hc45, hlam, hphi, ht23, ht34, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h269, h275, h276, hc03, hc45, hlam, hphi, ht34, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [hlam, p282_0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h273, hlam, p282_1]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          rcases p282_3 (m.d 0 1) (by simp) with h303 | h303
                          · linarith only [h140, h303, hlam]
                          · rcases p282_3 (m.d 0 2) (by simp) with h305 | h305
                            · linarith only [h143, h269, h275, h276, h305, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p282_1]
                            · linarith only [h142, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1, u0elo4]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [h142, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p282_1, u0elo4]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          rcases p282_3 (m.d 0 1) (by simp) with h309 | h309
                          · linarith only [h140, h309, hlam]
                          · rcases p282_3 (m.d 0 2) (by simp) with h311 | h311
                            · linarith only [h0, h143, h311, hc01, hc24, hlam, hphi, ht12, p282_1]
                            · linarith only [h142, h311, hlam]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht45, ht5b, p282_1, u0elo4, u4ehi0]
                        · have p282_0 := h282c.1
                          have p282_1 := h282c.2.1
                          have p282_2 := h282c.2.2.1
                          have p282_3 := h282c.2.2.2
                          linarith only [hlam, p282_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h316 | h316
                    · linarith only [h142, h143, h273, h275, h316, hc23, hc34, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h318 | h318
                      · linarith only [h100, h316, h318, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h275, h318, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h321 | h321
          · rcases m.htr 0 3 4 (by decide) (by decide) with h322 | h322
            · rcases m.htr 0 3 5 (by decide) (by decide) with h323 | h323
              · linarith only [h323, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h325 | h325
                · linarith only [h325, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h327 | h327
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                      · linarith only [h322, h323, h325, h329, hlam]
                      · linarith only [h142, h321, h323, h327, h328, h329, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                      · linarith only [h322, h328, h332, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h142, h321, h323, h332, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h322, h323, h327, hc13, hc35, hlam, hphi]
            · linarith only [h142, h321, h322, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
            · rcases m.htr 0 3 5 (by decide) (by decide) with h338 | h338
              · linarith only [h338, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
                · linarith only [h337, h338, h340, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h342 | h342
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h344 | h344
                      · linarith only [h321, h337, h340, h344, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h337, h338, h342, h343, h344, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h347 | h347
                      · linarith only [h337, h343, h347, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi1]
                      · linarith only [h337, h338, h347, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h337, h338, h342, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h351 | h351
              · linarith only [h351, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
                · linarith only [h353, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h357 | h357
                      · linarith only [h353, h355, h357, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h337, h355, h356, h357, hc01, hc13, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h100, h356, h360, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h0bigk with h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h0, h337, hc02, hc34, hlam, hphi, ht23, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h0, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h100, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h140, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h142, hc01, hc23, hlam, hphi, ht12, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h142, hlam, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h321, hlam, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht5b, p362_1, u0elo1, u5ehi0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h337, hc01, hc34, hlam, hphi, ht12, ht23, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h337, hc02, hc34, hlam, hphi, ht23, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h337, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h351, hlam, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h100, h356, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h100, h356, hc02, hc45, hlam, hphi, ht23, ht34, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h100, h356, hc03, hc45, hlam, hphi, ht34, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h353, hlam, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          rcases p362_3 (m.d 0 1) (by simp) with h383 | h383
                          · linarith only [h140, h383, hlam]
                          · rcases p362_3 (m.d 0 2) (by simp) with h385 | h385
                            · linarith only [h142, h385, hc01, hc23, hlam, hphi, ht12, p362_1]
                            · rcases p362_3 (m.d 0 3) (by simp) with h387 | h387
                              · linarith only [h351, h387, hlam]
                              · linarith only [h0, h387, hlam]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          rcases p362_3 (m.d 0 1) (by simp) with h390 | h390
                          · linarith only [h140, h390, hlam]
                          · rcases p362_3 (m.d 0 2) (by simp) with h392 | h392
                            · linarith only [h392, hlam, p362_0]
                            · rcases p362_3 (m.d 0 3) (by simp) with h394 | h394
                              · linarith only [h351, h394, hlam]
                              · linarith only [h142, h394, hlam]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          rcases p362_3 (m.d 0 1) (by simp) with h397 | h397
                          · linarith only [h140, h397, hlam]
                          · rcases p362_3 (m.d 0 2) (by simp) with h399 | h399
                            · linarith only [h142, h399, hlam, p362_1]
                            · rcases p362_3 (m.d 0 3) (by simp) with h401 | h401
                              · linarith only [h351, h401, hlam]
                              · rcases p362_3 (m.d 0 4) (by simp) with h403 | h403
                                · linarith only [h353, h403, hlam]
                                · linarith only [h337, h403, hlam]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht45, ht5b, p362_1, u0elo4, u4ehi0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                      · rcases h0bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h100, h355, hc02, hc34, hlam, hphi, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h0, hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h100, hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h140, hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h142, hc01, hc23, hlam, hphi, ht12, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h142, hlam, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h321, hlam, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h142, h337, h353, h355, h408, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p410_1, u5ehi0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h337, h353, h355, h408, hc01, hc34, hlam, hphi, ht12, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h337, h353, h355, h408, hc02, hc34, hlam, hphi, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h337, hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h351, hlam, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h353, h355, h408, hc01, hc34, hlam, hphi, ht12, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h353, h355, h408, hc02, hc34, hlam, hphi, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h353, h355, h408, hc03, hc34, hlam, hphi, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [hlam, p410_0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h353, hlam, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h353, h355, h408, hc01, hc34, hlam, hphi, ht12, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h353, h355, h408, hc02, hc34, hlam, hphi, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h0, h353, h355, h408, hc01, hc34, hlam, hphi, ht12, ht23, p410_1]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [h353, h355, h408, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p410_1, u4ehi0]
                        · have p410_0 := h410c.1
                          have p410_1 := h410c.2.1
                          have p410_2 := h410c.2.2.1
                          have p410_3 := h410c.2.2.2
                          linarith only [hlam, p410_0]
                      · linarith only [h355, h408, h409, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h437 | h437
                      · linarith only [h0, h355, h408, h437, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h355, h437, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

theorem n7l_sBT4_M_LI_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h10, h2, h7, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · linarith only [h10, h5, hc14, hlam, hphi, u4elo0]
                · linarith only [h6, h7, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, h3, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h16, h3, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h1, h18, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · linarith only [h18, h5, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
              · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h0, h23, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h25, h5, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                      · linarith only [h2, h21, h23, h27, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                        · linarith only [h27, h29, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                          · linarith only [h2, h22, h23, h31, h5, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h22, h23, h27, h31, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h21, h22, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                · linarith only [h0, h21, h3, h35, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h35, h4, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h39 | h39
          · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
              · linarith only [h3, h39, h40, h41, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h0, h44, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                    · linarith only [h1, h46, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · linarith only [h40, h46, hc14, hlam, hphi, u4elo0]
                · linarith only [h3, h39, h43, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
              · linarith only [h0, h3, h50, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                  · linarith only [h0, h53, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h40, h55, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                          · linarith only [h1, h40, h52, h59, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                          · linarith only [h52, h53, h57, h59, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h2, h40, h52, h53, h62, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h3, h39, h57, h58, h62, hc34, hlam, hphi, u4elo4]
                      · linarith only [h3, h57, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h3, h39, h52, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
            · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
              · linarith only [h0, h39, h68, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                · linarith only [h0, h39, h70, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
                  · linarith only [h0, h39, h72, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h1, h74, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · linarith only [h67, h74, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
              · linarith only [h0, h3, h77, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                · linarith only [h0, h39, h67, h79, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                  · linarith only [h0, h39, h67, h81, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
                    · linarith only [h39, h67, h83, hc02, hlam, hphi, ht23, ht34, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                          · linarith only [h0, h39, h67, h87, hc12, hlam, hphi, ht23, ht34, u4elo2]
                          · linarith only [h0, h39, h87, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                          · linarith only [h0, h39, h67, h90, hc12, hlam, hphi, ht23, ht34, u4elo2]
                          · linarith only [h0, h39, h90, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h3, h85, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h94 | h94
        · rcases m.htr 0 2 4 (by decide) (by decide) with h95 | h95
          · rcases m.htr 0 4 5 (by decide) (by decide) with h96 | h96
            · linarith only [h0, h2, h95, h96, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
              · linarith only [h0, h2, h96, h98, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h2, h94, h96, h98, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h94, h95, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h102 | h102
          · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
            · linarith only [h0, h102, h103, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
              · linarith only [h0, h105, h94, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                · linarith only [h0, h103, h107, h2, hc24, hlam, hphi, u4elo4]
                · linarith only [h102, h107, h94, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
            · linarith only [h1, h110, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
              · linarith only [h0, h102, h110, h112, hc23, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                · linarith only [h0, h102, h110, h114, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                  · linarith only [h1, h110, h114, h116, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
                    · linarith only [h1, h110, h118, h2, hlam]
                    · linarith only [h1, h114, h118, h2, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h122 | h122
    · rcases m.htr 0 1 5 (by decide) (by decide) with h123 | h123
      · rcases m.htr 0 2 3 (by decide) (by decide) with h124 | h124
        · rcases m.htr 0 2 4 (by decide) (by decide) with h125 | h125
          · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
            · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
              · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                    · linarith only [h122, h130, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · linarith only [h126, h128, h130, hc24, hlam, hphi, u4elo0]
                  · linarith only [h0, h122, h126, h129, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h122, h126, h128, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h0, h122, h124, h126, h127, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
              · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h126, h139, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                        · linarith only [h124, h142, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                          · linarith only [h0, h122, h126, h137, h144, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                            · linarith only [h126, h146, hc04, hlam, hphi, u4elo3]
                            · linarith only [h141, h142, h146, hc34, hlam, hphi, u4elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                        · linarith only [h122, h126, h137, h141, h149, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h151 | h151
                          · linarith only [h122, h126, h137, h151, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h153 | h153
                            · linarith only [h126, h153, hc04, hlam, hphi, u4elo3]
                            · linarith only [h141, h153, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h123, h138, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h123, h137, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h123, h136, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h124, h125, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h160 | h160
          · rcases m.htr 0 4 5 (by decide) (by decide) with h161 | h161
            · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
              · linarith only [h0, h122, h124, h161, h162, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h122, h161, h162, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
              · linarith only [h0, h123, h124, h165, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h123, h165, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h0, h123, h160, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h169 | h169
        · rcases m.htr 0 2 4 (by decide) (by decide) with h170 | h170
          · rcases m.htr 0 4 5 (by decide) (by decide) with h171 | h171
            · linarith only [h122, h123, h171, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
              · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                    · linarith only [h122, h171, h176, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h122, h123, h176, hc14, hlam, hphi, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h179 | h179
                    · linarith only [h122, h171, h179, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h122, h174, h175, h179, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h174, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h169, h173, hlam]
          · linarith only [h169, h170, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h185 | h185
          · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
            · linarith only [h122, h123, h186, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
              · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
                · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
                    · linarith only [h122, h123, h186, h191, hlam]
                    · linarith only [h122, h123, h191, hc14, hlam, hphi, u4elo4]
                  · linarith only [h0, h122, h169, h188, h189, h190, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h122, h169, h188, h189, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                    · linarith only [h122, h186, h198, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h122, h123, h198, hc14, hlam, hphi, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h122, h201, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · linarith only [h0, h122, h197, h201, hc14, hlam, hphi, u4elo4]
                · linarith only [h0, h122, h196, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h122, h185, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h206 | h206
      · linarith only [h122, h206, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h208 | h208
        · rcases m.htr 0 2 4 (by decide) (by decide) with h209 | h209
          · rcases m.htr 0 4 5 (by decide) (by decide) with h210 | h210
            · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
              · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
                · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h216 | h216
                        · linarith only [h208, h216, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h218 | h218
                          · linarith only [h208, h215, h218, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · linarith only [h210, h218, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                        · linarith only [h215, h221, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                          · linarith only [h209, h223, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · linarith only [h122, h210, h223, hc24, hlam, hphi, u4elo1]
                    · linarith only [h122, h210, h214, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                    · linarith only [h212, h213, h227, hlam]
                    · linarith only [h122, h209, h210, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h212, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h208, h211, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
              · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h235 | h235
                    · linarith only [h210, h235, hc04, hlam, hphi, u4elo1]
                    · linarith only [h122, h235, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h122, h210, h238, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h122, h238, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h208, h233, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h208, h232, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h208, h209, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h244 | h244
          · rcases m.htr 0 4 5 (by decide) (by decide) with h245 | h245
            · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
              · linarith only [h208, h244, h245, h246, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h248 | h248
                · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h252 | h252
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h253 | h253
                          · linarith only [h244, h253, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · linarith only [h122, h245, h253, hc24, hlam, hphi, u4elo1]
                        · linarith only [h246, h249, h252, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h244, h245, h246, h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h122, h245, h250, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                    · linarith only [h248, h249, h259, hlam]
                    · linarith only [h245, h259, hc14, hlam, hphi, u4elo0]
                · linarith only [h0, h244, h245, h248, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
              · rcases m.htr 1 2 4 (by decide) (by decide) with h264 | h264
                · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                    · linarith only [h245, h266, hc04, hlam, hphi, u4elo1]
                    · linarith only [h122, h266, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h208, h244, h263, h265, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h208, h244, h263, h264, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                · rcases m.htr 1 2 5 (by decide) (by decide) with h272 | h272
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                    · linarith only [h122, h245, h273, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h122, h273, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
                    · linarith only [h122, h245, h276, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h122, h276, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h244, h271, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
            · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
              · rcases m.htr 1 2 4 (by decide) (by decide) with h282 | h282
                · rcases m.htr 1 2 5 (by decide) (by decide) with h283 | h283
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
                            · linarith only [h281, h285, h288, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h244, h280, h282, h288, hc34, hlam, hphi, u4elo1]
                          · linarith only [h244, h280, h287, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h292 | h292
                          · linarith only [h285, h286, h292, hlam]
                          · linarith only [h244, h280, h292, hlam]
                      · linarith only [h0, h208, h285, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h280, h284, hc14, hlam, hphi, u4elo0]
                  · linarith only [h0, h208, h281, h283, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h208, h281, h282, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
                · linarith only [h0, h244, h281, h299, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h299, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
              · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
                · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                    · linarith only [h0, h244, h280, h305, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h122, h305, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h208, h302, h304, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h208, h302, h303, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
                · linarith only [h0, h244, h302, h310, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h310, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem n7l_sBT4_M_LI_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h4elo := hb4.1
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
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                  · linarith only [h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h6, h7, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, h3, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h14, h3, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h1, h16, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                    · linarith only [h16, h5, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h21, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                  · linarith only [h19, h21, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h19, h20, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h19, h25, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h25, h4, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h29 | h29
          · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
              · linarith only [h29, h3, h30, h31, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h0, h34, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                  · linarith only [h33, h34, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h29, h3, h33, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
              · linarith only [h0, h3, h38, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h0, h41, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
                  · linarith only [h40, h41, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h29, h3, h40, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
            · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
              · linarith only [h0, h29, h46, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                · linarith only [h0, h29, h48, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                  · linarith only [h0, h29, h50, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h1, h52, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                    · linarith only [h29, h45, h52, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
              · linarith only [h0, h3, h55, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                · linarith only [h0, h29, h45, h57, hc24, hlam, hphi, ht45, u5elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                  · linarith only [h0, h29, h45, h59, hlam, hphi, u5ehi7, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                    · linarith only [h29, h45, h61, hc02, hlam, hphi, ht23, ht34, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h0, h29, h45, h65, hc12, hlam, hphi, ht23, ht34, u4elo2]
                          · linarith only [h0, h29, h65, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h63, h64, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h3, h63, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h72 | h72
    · rcases m.htr 0 1 5 (by decide) (by decide) with h73 | h73
      · rcases m.htr 0 2 3 (by decide) (by decide) with h74 | h74
        · rcases m.htr 0 2 4 (by decide) (by decide) with h75 | h75
          · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
              · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h72, h80, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                    · linarith only [h76, h80, hc14, hlam, hphi, u4elo0]
                  · linarith only [h0, h79, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h72, h76, h78, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h0, h72, h74, h76, h77, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h76, h89, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                        · linarith only [h74, h92, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                        · linarith only [h91, h92, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                        · linarith only [h91, h95, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                          · linarith only [h72, h76, h87, h97, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                            · linarith only [h76, h99, hc04, hlam, hphi, u4elo3]
                            · linarith only [h91, h99, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h73, h88, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h73, h75, h87, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi6]
              · linarith only [h0, h73, h74, h86, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi6]
          · linarith only [h74, h75, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
            · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
              · linarith only [h0, h107, h108, h72, h74, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
              · linarith only [h0, h107, h108, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
              · linarith only [h0, h111, h73, h74, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
              · linarith only [h0, h111, h73, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h106, h73, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi6]
      · linarith only [h72, h73, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h116 | h116
      · linarith only [h116, h72, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi6]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h118 | h118
        · rcases m.htr 0 2 4 (by decide) (by decide) with h119 | h119
          · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                        · linarith only [h118, h126, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                        · linarith only [h125, h126, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                        · linarith only [h125, h129, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                          · linarith only [h119, h131, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                          · linarith only [h120, h131, hc24, hlam, hphi, u4elo0]
                    · linarith only [h120, h124, h72, hlam]
                  · linarith only [h0, h123, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h122, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h118, h121, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
              · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                    · linarith only [h120, h141, hc04, hlam, hphi, u4elo1]
                    · linarith only [h141, h72, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h140, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h119, h139, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h118, h138, hlam]
          · linarith only [h118, h119, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h148 | h148
          · rcases m.htr 0 4 5 (by decide) (by decide) with h149 | h149
            · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
              · linarith only [h118, h148, h149, h150, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                          · linarith only [h148, h157, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                          · linarith only [h149, h157, h72, hc24, hlam, hphi, u4elo1]
                        · linarith only [h150, h153, h156, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h0, h148, h149, h150, h155, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · linarith only [h149, h154, h72, hlam]
                  · linarith only [h0, h148, h149, h153, hlam, hphi, u5ehi9, u5elo2]
                · linarith only [h0, h148, h149, h152, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                    · linarith only [h149, h168, hc04, hlam, hphi, u4elo1]
                    · linarith only [h168, h72, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h118, h148, h165, h167, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h118, h148, h165, h166, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                    · linarith only [h149, h175, h72, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h175, h72, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h174, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h148, h173, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h180 | h180
            · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
              · rcases m.htr 1 2 4 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h181, h185, h188, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · linarith only [h148, h180, h182, h188, hc34, hlam, hphi, u4elo1]
                          · linarith only [h148, h180, h187, hlam]
                        · linarith only [h118, h186, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h118, h185, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h148, h180, h182, h184, hlam]
                  · linarith only [h0, h183, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h118, h181, h182, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
                · linarith only [h148, h180, h181, h197, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · linarith only [h0, h197, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
              · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                · rcases m.htr 1 2 5 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                    · linarith only [h0, h148, h180, h203, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h203, h72, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h118, h200, h202, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h118, h200, h201, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                · linarith only [h0, h148, h200, h208, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h208, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem n7l_sBT4_M_LI_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
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
            · linarith only [h7, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h5, h6, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h11 | h11
          · rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
            · linarith only [h12, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h12, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h11, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h17 | h17
    · rcases p0_3 (m.d 0 2) (by simp) with h18 | h18
      · rcases p0_3 (m.d 0 3) (by simp) with h19 | h19
        · linarith only [h19, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · linarith only [h22, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h22, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h21, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · linarith only [h18, h29, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h29, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h28, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
    · linarith only [h17, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 0 3) (by simp) with h39 | h39
        · rcases p0_3 (m.d 0 4) (by simp) with h40 | h40
          · rcases p0_3 (m.d 0 5) (by simp) with h41 | h41
            · linarith only [h41, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h41, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h40, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
          · rcases p0_3 (m.d 0 5) (by simp) with h46 | h46
            · linarith only [h46, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h46, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h45, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
      · linarith only [h38, hlam, p0_0]
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
            · linarith only [h52, h57, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h52, h56, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h62 | h62
      · rcases p0_3 (m.d 0 3) (by simp) with h63 | h63
        · linarith only [h63, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h65 | h65
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · linarith only [h52, h66, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h66, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h65, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
      · linarith only [h62, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h73 | h73
    · linarith only [h73, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h75 | h75
      · rcases p0_3 (m.d 0 3) (by simp) with h76 | h76
        · rcases p0_3 (m.d 0 4) (by simp) with h77 | h77
          · rcases p0_3 (m.d 0 5) (by simp) with h78 | h78
            · linarith only [h78, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h78, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · linarith only [h77, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
        · linarith only [h76, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h83 | h83
        · rcases p0_3 (m.d 0 4) (by simp) with h84 | h84
          · rcases p0_3 (m.d 0 5) (by simp) with h85 | h85
            · linarith only [h85, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h85, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · linarith only [h84, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
        · linarith only [h83, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h90 | h90
    · rcases p0_3 (m.d 0 2) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h93 | h93
        · rcases p0_3 (m.d 0 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 0 5) (by simp) with h95 | h95
            · linarith only [h95, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h90, h95, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h90, h94, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h100 | h100
      · linarith only [h100, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h102 | h102
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · linarith only [h104, h90, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h104, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · linarith only [h103, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
        · linarith only [h102, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h114 | h114
      · rcases p0_3 (m.d 0 3) (by simp) with h115 | h115
        · rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 0 5) (by simp) with h117 | h117
            · linarith only [h117, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h114, h117, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h116, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 0 5) (by simp) with h122 | h122
            · linarith only [h122, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h114, h122, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h126 | h126
        · rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
          · rcases p0_3 (m.d 0 5) (by simp) with h128 | h128
            · linarith only [h128, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h126, h128, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · linarith only [h127, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · rcases p0_3 (m.d 0 5) (by simp) with h133 | h133
            · linarith only [h133, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h133, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h132, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h137 | h137
    · rcases p0_3 (m.d 0 2) (by simp) with h138 | h138
      · linarith only [h138, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h140 | h140
        · rcases p0_3 (m.d 0 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 0 5) (by simp) with h142 | h142
            · linarith only [h142, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h137, h142, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h137, h147, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h151 | h151
      · linarith only [h151, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h153 | h153
        · rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
          · rcases p0_3 (m.d 0 5) (by simp) with h155 | h155
            · linarith only [h137, h155, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h153, h155, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · linarith only [h160, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h160, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h159, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h164 | h164
    · rcases p0_3 (m.d 0 2) (by simp) with h165 | h165
      · rcases p0_3 (m.d 0 3) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 0 5) (by simp) with h169 | h169
            · linarith only [h169, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h164, h169, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h168, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h173 | h173
        · linarith only [h173, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 0 5) (by simp) with h176 | h176
            · linarith only [h165, h176, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h164, h176, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h175, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h180 | h180
      · rcases p0_3 (m.d 0 3) (by simp) with h181 | h181
        · linarith only [h181, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h183 | h183
          · rcases p0_3 (m.d 0 5) (by simp) with h184 | h184
            · linarith only [h164, h184, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h180, h184, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h183, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h188 | h188
        · linarith only [h188, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h190 | h190
          · rcases p0_3 (m.d 0 5) (by simp) with h191 | h191
            · linarith only [h164, h191, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h191, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h190, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
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
    linarith only [hlam, hphi, ht45, p0_1, u4ehi0, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
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
  have h5emax := hb5.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h0, h3, h6, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, h2, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h12, h14, h2, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h1, h16, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h0, h16, h2, h4, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h20, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h0, h19, h20, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h19, h2, h25, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h0, h2, h25, h27, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h29, h5, hc14, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h19, h2, h25, h31, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h19, h2, h31, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
            · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
              · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                · linarith only [h0, h36, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h0, h3, h35, h36, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                · linarith only [h0, h39, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h4, h41, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h3, h39, h44, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h34, h44, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                      · linarith only [h1, h47, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h0, h3, h34, h47, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
              · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                · linarith only [h0, h51, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h0, h3, h50, h51, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h54, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h4, h56, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                      · linarith only [h34, h59, hc14, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h56, h58, h59, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h0, h3, h34, h4, h54, h62, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                        · linarith only [h0, h2, h4, h64, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
                          · linarith only [h0, h3, h58, h64, h66, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                            · linarith only [h0, h3, h34, h4, h68, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                              · linarith only [h34, h4, h70, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                              · linarith only [h0, h3, h4, h50, h64, h70, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h73 | h73
          · linarith only [h2, h3, h73, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
            · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
              · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                · linarith only [h3, h77, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                  · linarith only [h73, h79, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                      · linarith only [h1, h82, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h75, h82, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h1, h85, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h1, h75, h85, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
              · linarith only [h2, h3, h76, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
              · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                · linarith only [h0, h2, h3, h75, h90, hc45, hlam, hphi, u0ehi7, u0elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                  · linarith only [h73, h92, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                      · linarith only [h1, h2, h3, h75, h95, hlam, hphi, u0ehi7, u0elo0]
                      · linarith only [h89, h90, h94, h95, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                      · linarith only [h1, h2, h3, h75, h98, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                        · linarith only [h1, h100, h73, h89, h90, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h1, h102, h2, h3, h75, h89, h90, h94, hc13, hc45, hlam, hphi, ht34, u0ehi7, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                            · linarith only [h104, h2, h3, h75, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                            · linarith only [h104, h2, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h2, h3, h89, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h108 | h108
        · rcases m.htr 0 3 4 (by decide) (by decide) with h109 | h109
          · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
              · linarith only [h108, h111, h2, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                · linarith only [h0, h113, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h108, h113, h2, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
              · linarith only [h108, h116, h2, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                · linarith only [h0, h118, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h108, h118, h2, hc12, hc23, hlam, hphi]
          · linarith only [h108, h109, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h122 | h122
          · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
            · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
              · linarith only [h124, h2, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                · linarith only [h0, h108, h126, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h1, h130, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h123, h130, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
                      · linarith only [h1, h133, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h1, h123, h133, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                    · linarith only [h122, h128, h136, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h1, h138, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h1, h123, h138, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
              · linarith only [h141, h2, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
                · linarith only [h0, h108, h143, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
                      · linarith only [h1, h123, h147, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h150 | h150
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h151 | h151
                            · linarith only [h108, h123, h149, h151, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                            · linarith only [h108, h151, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                          · linarith only [h146, h150, h2, hc13, hlam, hphi, ht01, u0ehi6]
                        · linarith only [h149, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                      · linarith only [h1, h156, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                          · linarith only [h145, h146, h159, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h159, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h145, h158, h2, hc13, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                    · linarith only [h122, h145, h163, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                      · linarith only [h108, h122, h123, h145, h165, hlam, hphi, u0ehi6, u0elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h169 | h169
                            · linarith only [h108, h123, h169, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                            · linarith only [h108, h169, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                          · linarith only [h168, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h122, h167, h2, hlam, hphi, u0ehi6, u0elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h174 | h174
            · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
              · linarith only [h175, h2, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                · linarith only [h0, h108, h177, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                  · linarith only [h122, h179, h2, hc13, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                      · linarith only [h1, h182, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h174, h182, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                      · linarith only [h1, h185, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h1, h174, h185, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
              · linarith only [h188, h2, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                · linarith only [h0, h108, h190, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                  · linarith only [h122, h192, h2, hc13, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                      · linarith only [h1, h174, h195, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                      · linarith only [h192, h194, h195, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                      · linarith only [h1, h122, h174, h198, h2, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                        · linarith only [h122, h2, h200, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h2, h200, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h203 | h203
      · rcases m.htr 0 2 4 (by decide) (by decide) with h204 | h204
        · linarith only [h0, h1, h204, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h206 | h206
          · linarith only [h0, h1, h203, h206, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h208 | h208
            · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
              · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                · linarith only [h0, h204, h210, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h212 | h212
                  · linarith only [h0, h1, h206, h209, h210, h212, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                  · linarith only [h0, h1, h209, h212, hc23, hc34, hlam, hphi]
              · linarith only [h203, h204, h209, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
              · linarith only [h0, h1, h208, h216, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h1, h203, h208, h216, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h219 | h219
        · linarith only [h0, h1, h219, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h221 | h221
          · rcases m.htr 0 4 5 (by decide) (by decide) with h222 | h222
            · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
              · linarith only [h203, h223, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                · linarith only [h0, h219, h225, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h231 | h231
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                              · linarith only [h221, h233, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                              · linarith only [h221, h222, h233, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
                            · linarith only [h221, h222, h232, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                          · linarith only [h0, h1, h223, h227, h231, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h223, h227, h230, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · linarith only [h0, h1, h221, h222, h229, hlam, hphi, u0ehi6, u0elo2]
                    · linarith only [h0, h1, h227, h228, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h0, h1, h221, h227, hlam, hphi, u0ehi6, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
              · linarith only [h203, h242, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                · linarith only [h0, h244, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h247 | h247
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                      · linarith only [h0, h1, h222, h246, h248, hc13, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h1, h248, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h0, h1, h246, h247, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h0, h1, h221, h246, hlam, hphi, u0ehi6, u0elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
            · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
              · linarith only [h0, h203, h254, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                · linarith only [h0, h256, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h258 | h258
                  · linarith only [h221, h258, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h260 | h260
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
                        · linarith only [h0, h1, h258, h262, hc12, hc23, hlam, hphi]
                        · linarith only [h203, h262, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · linarith only [h0, h1, h253, h261, hlam, hphi, u0ehi6, u0elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                        · linarith only [h203, h221, h267, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h203, h267, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · linarith only [h0, h1, h253, h266, hlam, hphi, u0ehi6, u0elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
              · linarith only [h0, h203, h271, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                · linarith only [h0, h1, h253, h273, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                  · linarith only [h203, h221, h275, hc13, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                      · linarith only [h253, h278, hc14, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h0, h1, h278, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                      · linarith only [h0, h1, h253, h281, hc14, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h1, h281, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h284 | h284
    · rcases m.htr 0 2 3 (by decide) (by decide) with h285 | h285
      · rcases m.htr 0 2 4 (by decide) (by decide) with h286 | h286
        · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
          · rcases m.htr 0 4 5 (by decide) (by decide) with h288 | h288
            · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
              · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
                · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h284, h293, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h287, h288, h293, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h284, h296, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · linarith only [h0, h284, h288, h296, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h285, h287, h291, h299, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
                      · linarith only [h0, h284, h301, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · linarith only [h0, h284, h288, h301, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                · linarith only [h0, h290, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h284, h288, h289, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
              · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
                · rcases m.htr 1 3 4 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                      · linarith only [h284, h288, h310, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                        · linarith only [h285, h312, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h314 | h314
                          · linarith only [h285, h287, h312, h314, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h316 | h316
                            · linarith only [h288, h316, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h318 | h318
                              · linarith only [h0, h284, h288, h308, h318, hc12, hlam, hphi, ht01, u0ehi8]
                              · rcases h5emax with h320 | h320 | h320 | h320 | h320
                                · linarith only [h288, h320, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi8]
                                · linarith only [h309, h318, h320, hlam, ht45, u4ehi3]
                                · linarith only [h316, h320, hlam, ht45, u4ehi2]
                                · linarith only [h318, h320, hlam, ht45, u4ehi3]
                                · linarith only [h288, h320, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h326 | h326
                      · linarith only [h0, h284, h288, h326, hc12, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h328 | h328
                        · linarith only [h285, h328, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · linarith only [h308, h309, h328, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h285, h287, h308, h331, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                      · linarith only [h0, h284, h288, h333, hc12, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                        · linarith only [h285, h308, h335, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h337 | h337
                          · linarith only [h285, h287, h306, h308, h331, h337, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                            · linarith only [h288, h339, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
                              · linarith only [h285, h287, h288, h341, hlam, hphi, u0ehi8, u0elo1]
                              · rcases h5emax with h343 | h343 | h343 | h343 | h343
                                · linarith only [h288, h343, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi8]
                                · linarith only [h333, h343, hlam, ht45, u4ehi1]
                                · linarith only [h339, h343, hlam, ht45, u4ehi2]
                                · linarith only [h307, h331, h333, h343, hlam, ht45, u4ehi2]
                                · linarith only [h288, h343, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi8]
                · linarith only [h0, h307, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h284, h306, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
            · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
              · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
                · rcases m.htr 1 3 4 (by decide) (by decide) with h354 | h354
                  · linarith only [h287, h354, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h357 | h357
                      · linarith only [h284, h357, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h351, h357, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h0, h284, h360, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h284, h351, h360, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h353, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h284, h351, h352, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
              · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
                · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
                  · linarith only [h287, h367, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h369 | h369
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                      · linarith only [h284, h351, h370, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                      · linarith only [h367, h369, h370, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h284, h287, h351, h373, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                        · linarith only [h0, h284, h365, h367, h375, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                          · linarith only [h285, h369, h377, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h379 | h379
                            · linarith only [h0, h284, h287, h351, h366, h379, hc12, hlam, hphi, ht01, u0ehi7]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h381 | h381
                              · linarith only [h287, h351, h381, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                              · linarith only [h287, h381, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h0, h284, h366, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h284, h287, h351, h365, hc23, hc45, hlam, hphi, ht01, ht12, u0ehi7, u4ehi1]
        · linarith only [h0, h284, h286, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h387 | h387
        · rcases m.htr 0 3 4 (by decide) (by decide) with h388 | h388
          · rcases m.htr 0 4 5 (by decide) (by decide) with h389 | h389
            · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
              · linarith only [h285, h387, h390, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h284, h389, h390, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h393 | h393
              · linarith only [h0, h285, h393, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h284, h393, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h284, h285, h388, hlam]
        · linarith only [h0, h284, h387, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h398 | h398
      · rcases m.htr 0 2 4 (by decide) (by decide) with h399 | h399
        · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
          · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
            · rcases m.htr 1 2 3 (by decide) (by decide) with h402 | h402
              · rcases m.htr 1 2 4 (by decide) (by decide) with h403 | h403
                · rcases m.htr 1 3 4 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h405 | h405
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                        · linarith only [h398, h407, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                          · linarith only [h398, h400, h407, h409, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                            · linarith only [h398, h400, h407, h411, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                            · linarith only [h401, h411, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                      · linarith only [h284, h398, h400, h401, h406, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h284, h404, h405, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h284, h398, h400, h404, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h403, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h402, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
              · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
                · rcases m.htr 1 3 4 (by decide) (by decide) with h421 | h421
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h423 | h423
                      · linarith only [h401, h419, h421, h423, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h284, h423, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                    · linarith only [h284, h421, h422, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h284, h398, h400, h421, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h399, h420, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h419, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h430 | h430
            · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
              · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
                · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                  · linarith only [h400, h433, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                        · linarith only [h398, h433, h437, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h439 | h439
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h440 | h440
                            · linarith only [h399, h440, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                            · linarith only [h430, h440, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                          · linarith only [h433, h435, h439, hc23, hc34, hlam, hphi]
                      · linarith only [h284, h399, h430, h436, hlam, hphi, u0ehi5, u0elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                        · linarith only [h398, h433, h446, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                          · linarith only [h398, h435, h445, h448, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                            · linarith only [h399, h450, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                            · linarith only [h399, h430, h450, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                      · linarith only [h284, h399, h430, h445, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h432, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h431, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
              · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
                · rcases m.htr 1 3 4 (by decide) (by decide) with h458 | h458
                  · linarith only [h400, h458, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h461 | h461
                      · linarith only [h430, h458, h461, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · linarith only [h284, h461, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
                      · linarith only [h284, h430, h464, hc14, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h284, h464, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                · linarith only [h0, h399, h457, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h398, h456, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h469 | h469
          · linarith only [h398, h399, h469, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h471 | h471
            · rcases m.htr 1 2 3 (by decide) (by decide) with h472 | h472
              · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                · linarith only [h399, h473, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h473, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h398, h472, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
              · rcases m.htr 1 2 4 (by decide) (by decide) with h478 | h478
                · linarith only [h399, h478, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h478, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h398, h399, h471, h477, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h482 | h482
        · rcases m.htr 0 3 4 (by decide) (by decide) with h483 | h483
          · rcases m.htr 0 4 5 (by decide) (by decide) with h484 | h484
            · rcases m.htr 1 2 3 (by decide) (by decide) with h485 | h485
              · linarith only [h398, h482, h484, h485, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h0, h485, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
              · linarith only [h398, h482, h488, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h488, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h398, h482, h483, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h492 | h492
          · rcases m.htr 0 4 5 (by decide) (by decide) with h493 | h493
            · rcases m.htr 1 2 3 (by decide) (by decide) with h494 | h494
              · linarith only [h398, h494, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h494, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
              · linarith only [h0, h398, h497, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h497, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h500 | h500
            · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
              · linarith only [h0, h398, h501, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h501, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
              · linarith only [h0, h398, h504, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h504, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
