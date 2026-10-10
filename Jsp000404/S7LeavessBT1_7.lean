import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT1_H_I_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
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
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases m.htr 0 1 2 (by decide) (by decide) with h23 | h23
              · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h22, h25, hlam]
                  · linarith only [h25, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h23, h24, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h23, hlam, p0_0]
            · linarith only [h22, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h31 | h31
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h31, h34, hlam]
                  · linarith only [h34, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h32, h33, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h32, hlam, p0_0]
            · linarith only [h31, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h41 | h41
    · rcases p0_3 (m.d 0 2) (by simp) with h42 | h42
      · rcases p0_3 (m.d 0 3) (by simp) with h43 | h43
        · linarith only [h43, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
          · rcases p0_3 (m.d 0 5) (by simp) with h46 | h46
            · rcases m.htr 0 1 2 (by decide) (by decide) with h47 | h47
              · linarith only [h42, h47, hlam]
              · linarith only [h47, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h46, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h51 | h51
            · rcases m.htr 0 1 2 (by decide) (by decide) with h52 | h52
              · linarith only [h42, h52, hlam]
              · linarith only [h52, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h51, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
          · rcases p0_3 (m.d 0 5) (by simp) with h59 | h59
            · rcases m.htr 0 1 2 (by decide) (by decide) with h60 | h60
              · rcases m.htr 0 1 3 (by decide) (by decide) with h61 | h61
                · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
                  · linarith only [h59, h62, hlam]
                  · linarith only [h42, h62, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h61, hlam, p0_0]
              · linarith only [h42, h60, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h59, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h68 | h68
            · rcases m.htr 0 1 2 (by decide) (by decide) with h69 | h69
              · rcases m.htr 0 1 3 (by decide) (by decide) with h70 | h70
                · rcases m.htr 0 1 5 (by decide) (by decide) with h71 | h71
                  · linarith only [h68, h71, hlam]
                  · linarith only [h71, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h70, hlam, p0_0]
              · linarith only [h42, h69, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h68, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h41, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h78 | h78
    · rcases p0_3 (m.d 0 2) (by simp) with h79 | h79
      · rcases p0_3 (m.d 0 3) (by simp) with h80 | h80
        · rcases p0_3 (m.d 0 4) (by simp) with h81 | h81
          · linarith only [h81, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h83 | h83
            · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
              · linarith only [h79, h84, hlam]
              · linarith only [h84, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h83, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
          · linarith only [h88, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h90 | h90
            · rcases m.htr 0 1 2 (by decide) (by decide) with h91 | h91
              · linarith only [h79, h91, hlam]
              · linarith only [h80, h91, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h90, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h95 | h95
        · rcases p0_3 (m.d 0 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h98 | h98
            · rcases m.htr 0 1 2 (by decide) (by decide) with h99 | h99
              · rcases m.htr 0 1 3 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h95, hlam]
                · linarith only [h100, h79, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h79, h99, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h98, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 1 3 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 1 5 (by decide) (by decide) with h110 | h110
                  · linarith only [h107, h110, hlam]
                  · linarith only [h110, h95, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h108, h109, h79, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h108, h79, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h107, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h78, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h118 | h118
    · linarith only [h118, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h120 | h120
      · rcases p0_3 (m.d 0 3) (by simp) with h121 | h121
        · rcases p0_3 (m.d 0 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 0 5) (by simp) with h123 | h123
            · rcases m.htr 0 1 2 (by decide) (by decide) with h124 | h124
              · linarith only [h124, hlam, p0_0]
              · linarith only [h124, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h123, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h128 | h128
            · rcases m.htr 0 1 2 (by decide) (by decide) with h129 | h129
              · linarith only [h129, hlam, p0_0]
              · linarith only [h129, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h128, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
              · linarith only [h135, hlam, p0_0]
              · linarith only [h135, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h139 | h139
            · rcases m.htr 0 1 2 (by decide) (by decide) with h140 | h140
              · linarith only [h140, hlam, p0_0]
              · linarith only [h140, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h139, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h120, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h146 | h146
    · rcases p0_3 (m.d 0 2) (by simp) with h147 | h147
      · rcases p0_3 (m.d 0 3) (by simp) with h148 | h148
        · linarith only [h148, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h150 | h150
          · rcases p0_3 (m.d 0 5) (by simp) with h151 | h151
            · rcases m.htr 0 1 2 (by decide) (by decide) with h152 | h152
              · rcases m.htr 0 1 3 (by decide) (by decide) with h153 | h153
                · rcases m.htr 0 1 5 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h156 | h156
                      · linarith only [h150, h156, hlam]
                      · linarith only [h156, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h155, hlam, p0_0]
                  · linarith only [h152, h153, h154, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h152, h153, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h152, hlam]
            · linarith only [h151, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h164 | h164
            · rcases m.htr 0 1 2 (by decide) (by decide) with h165 | h165
              · rcases m.htr 0 1 3 (by decide) (by decide) with h166 | h166
                · rcases m.htr 0 1 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h169 | h169
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h170 | h170
                        · linarith only [h164, h170, hlam]
                        · linarith only [h170, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h166, h169, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h168, hlam, p0_0]
                  · linarith only [h165, h166, h167, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h165, h166, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h165, hlam]
            · linarith only [h146, h164, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h147, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h180 | h180
      · rcases p0_3 (m.d 0 3) (by simp) with h181 | h181
        · linarith only [h181, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h183 | h183
          · rcases p0_3 (m.d 0 5) (by simp) with h184 | h184
            · rcases m.htr 0 1 2 (by decide) (by decide) with h185 | h185
              · linarith only [h146, h185, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h185, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h184, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h189 | h189
            · rcases m.htr 0 1 2 (by decide) (by decide) with h190 | h190
              · linarith only [h146, h190, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h190, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h189, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h180, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h195 | h195
    · rcases p0_3 (m.d 0 2) (by simp) with h196 | h196
      · rcases p0_3 (m.d 0 3) (by simp) with h197 | h197
        · rcases p0_3 (m.d 0 4) (by simp) with h198 | h198
          · linarith only [h198, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h200 | h200
            · rcases m.htr 0 1 2 (by decide) (by decide) with h201 | h201
              · rcases m.htr 0 1 3 (by decide) (by decide) with h202 | h202
                · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h204 | h204
                    · linarith only [h197, h204, hlam]
                    · linarith only [h204, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · linarith only [h201, h203, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h201, h202, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h195, h201, hlam]
            · linarith only [h200, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h211 | h211
          · linarith only [h211, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h213 | h213
            · rcases m.htr 0 1 2 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 1 3 (by decide) (by decide) with h215 | h215
                · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h217 | h217
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h218 | h218
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h219 | h219
                        · linarith only [h213, h219, hlam]
                        · linarith only [h197, h215, h219, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h218, hlam, p0_0]
                    · linarith only [h197, h215, h217, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h197, h214, h215, h216, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h197, h214, h215, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h195, h214, hlam]
            · linarith only [h195, h213, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h196, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h229 | h229
      · rcases p0_3 (m.d 0 3) (by simp) with h230 | h230
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · linarith only [h231, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h233 | h233
            · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
              · linarith only [h195, h234, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h195, h234, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h233, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h238 | h238
          · linarith only [h238, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h240 | h240
            · rcases m.htr 0 1 2 (by decide) (by decide) with h241 | h241
              · linarith only [h195, h241, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h195, h241, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h240, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h229, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h247 | h247
    · linarith only [h247, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h249 | h249
      · rcases p0_3 (m.d 0 3) (by simp) with h250 | h250
        · rcases p0_3 (m.d 0 4) (by simp) with h251 | h251
          · rcases p0_3 (m.d 0 5) (by simp) with h252 | h252
            · rcases m.htr 0 1 2 (by decide) (by decide) with h253 | h253
              · linarith only [h253, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h249, h253, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h249, h252, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h257 | h257
            · rcases m.htr 0 1 2 (by decide) (by decide) with h258 | h258
              · linarith only [h249, h258, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h249, h258, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h249, h257, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h250, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h263 | h263
        · rcases p0_3 (m.d 0 4) (by simp) with h264 | h264
          · rcases p0_3 (m.d 0 5) (by simp) with h265 | h265
            · rcases m.htr 0 1 2 (by decide) (by decide) with h266 | h266
              · linarith only [h266, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h249, h266, hlam]
            · linarith only [h265, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h270 | h270
            · rcases m.htr 0 1 2 (by decide) (by decide) with h271 | h271
              · linarith only [h271, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h249, h271, hlam]
            · linarith only [h270, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h276 | h276
    · rcases p0_3 (m.d 0 2) (by simp) with h277 | h277
      · linarith only [h277, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h279 | h279
        · rcases p0_3 (m.d 0 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 0 5) (by simp) with h281 | h281
            · rcases m.htr 0 1 2 (by decide) (by decide) with h282 | h282
              · rcases m.htr 0 1 3 (by decide) (by decide) with h283 | h283
                · rcases m.htr 0 1 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h285 | h285
                    · linarith only [h285, hlam, p0_0]
                    · linarith only [h285, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h282, h283, h284, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h276, h283, hlam]
              · linarith only [h276, h282, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h276, h281, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h292 | h292
            · rcases m.htr 0 1 2 (by decide) (by decide) with h293 | h293
              · rcases m.htr 0 1 3 (by decide) (by decide) with h294 | h294
                · rcases m.htr 0 1 5 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h296 | h296
                    · linarith only [h296, hlam, p0_0]
                    · linarith only [h296, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h293, h294, h295, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h276, h294, hlam]
              · linarith only [h276, h293, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h276, h292, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h304 | h304
      · linarith only [h304, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h306 | h306
        · rcases p0_3 (m.d 0 4) (by simp) with h307 | h307
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · linarith only [h276, h309, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h311 | h311
                · linarith only [h309, h311, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h309, h311, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h308, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h315 | h315
            · rcases m.htr 0 1 2 (by decide) (by decide) with h316 | h316
              · linarith only [h276, h316, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h318 | h318
                · linarith only [h316, h318, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h316, h318, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h315, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h306, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h324 | h324
    · rcases p0_3 (m.d 0 2) (by simp) with h325 | h325
      · rcases p0_3 (m.d 0 3) (by simp) with h326 | h326
        · rcases p0_3 (m.d 0 4) (by simp) with h327 | h327
          · linarith only [h327, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h329 | h329
            · rcases m.htr 0 1 2 (by decide) (by decide) with h330 | h330
              · rcases m.htr 0 1 3 (by decide) (by decide) with h331 | h331
                · rcases m.htr 0 1 5 (by decide) (by decide) with h332 | h332
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h333 | h333
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h334 | h334
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h335 | h335
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h336 | h336
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h337 | h337
                            · linarith only [h329, h337, hlam]
                            · linarith only [h334, h337, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                          · linarith only [h336, hlam, p0_0]
                        · linarith only [h333, h334, h335, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h333, h334, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h325, h333, hlam]
                  · linarith only [h331, h332, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h324, h331, hlam]
              · linarith only [h324, h330, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h324, h329, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h326, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h349 | h349
        · rcases p0_3 (m.d 0 4) (by simp) with h350 | h350
          · linarith only [h350, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h352 | h352
            · rcases m.htr 0 1 2 (by decide) (by decide) with h353 | h353
              · rcases m.htr 0 1 3 (by decide) (by decide) with h354 | h354
                · rcases m.htr 0 1 5 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h356 | h356
                    · linarith only [h325, h354, h356, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h325, h353, h356, hc12, hc23, hlam, hphi, p0_1]
                  · linarith only [h325, h353, h354, h355, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h324, h354, hlam]
              · linarith only [h324, h325, h353, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h324, h352, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h349, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h364 | h364
      · rcases p0_3 (m.d 0 3) (by simp) with h365 | h365
        · rcases p0_3 (m.d 0 4) (by simp) with h366 | h366
          · linarith only [h366, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h368 | h368
            · rcases m.htr 0 1 2 (by decide) (by decide) with h369 | h369
              · linarith only [h324, h369, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h324, h364, h369, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h364, h368, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h365, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h374 | h374
        · rcases p0_3 (m.d 0 4) (by simp) with h375 | h375
          · linarith only [h375, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h377 | h377
            · rcases m.htr 0 1 2 (by decide) (by decide) with h378 | h378
              · linarith only [h324, h378, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h380 | h380
                · linarith only [h364, h378, h380, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h364, h378, h380, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h377, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h374, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h386 | h386
    · linarith only [h386, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h388 | h388
      · rcases p0_3 (m.d 0 3) (by simp) with h389 | h389
        · rcases p0_3 (m.d 0 4) (by simp) with h390 | h390
          · rcases p0_3 (m.d 0 5) (by simp) with h391 | h391
            · rcases m.htr 0 1 2 (by decide) (by decide) with h392 | h392
              · linarith only [h388, h392, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h388, h392, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h388, h391, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h390, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h397 | h397
          · rcases p0_3 (m.d 0 5) (by simp) with h398 | h398
            · rcases m.htr 0 1 2 (by decide) (by decide) with h399 | h399
              · linarith only [h388, h399, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h388, h399, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h388, h398, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h397, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h404 | h404
        · rcases p0_3 (m.d 0 4) (by simp) with h405 | h405
          · rcases p0_3 (m.d 0 5) (by simp) with h406 | h406
            · rcases m.htr 0 1 2 (by decide) (by decide) with h407 | h407
              · linarith only [h407, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h388, h407, hlam]
            · linarith only [h406, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h405, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h412 | h412
          · rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
            · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
              · linarith only [h414, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h388, h414, hlam]
            · linarith only [h413, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h412, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h419 | h419
    · rcases p0_3 (m.d 0 2) (by simp) with h420 | h420
      · linarith only [h420, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h422 | h422
        · rcases p0_3 (m.d 0 4) (by simp) with h423 | h423
          · rcases p0_3 (m.d 0 5) (by simp) with h424 | h424
            · rcases m.htr 0 1 2 (by decide) (by decide) with h425 | h425
              · rcases m.htr 0 1 3 (by decide) (by decide) with h426 | h426
                · rcases m.htr 0 1 5 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h428 | h428
                    · linarith only [h422, h426, h428, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h422, h428, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h422, h425, h426, h427, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h419, h425, h426, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h419, h425, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h419, h424, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h423, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h436 | h436
          · rcases p0_3 (m.d 0 5) (by simp) with h437 | h437
            · rcases m.htr 0 1 2 (by decide) (by decide) with h438 | h438
              · rcases m.htr 0 1 3 (by decide) (by decide) with h439 | h439
                · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h441 | h441
                    · linarith only [h437, h440, h441, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h422, h441, hlam]
                  · linarith only [h419, h438, h440, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h419, h438, h439, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h419, h438, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h419, h437, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h436, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h449 | h449
      · linarith only [h449, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h451 | h451
        · rcases p0_3 (m.d 0 4) (by simp) with h452 | h452
          · rcases p0_3 (m.d 0 5) (by simp) with h453 | h453
            · rcases m.htr 0 1 2 (by decide) (by decide) with h454 | h454
              · linarith only [h419, h454, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h456 | h456
                · linarith only [h454, h456, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h451, h454, h456, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h453, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h452, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h461 | h461
          · rcases p0_3 (m.d 0 5) (by simp) with h462 | h462
            · rcases m.htr 0 1 2 (by decide) (by decide) with h463 | h463
              · linarith only [h419, h463, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h465 | h465
                · linarith only [h463, h465, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h467 | h467
                  · linarith only [h463, h467, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h462, h463, h467, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h462, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h461, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h472 | h472
    · rcases p0_3 (m.d 0 2) (by simp) with h473 | h473
      · rcases p0_3 (m.d 0 3) (by simp) with h474 | h474
        · linarith only [h474, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h476 | h476
          · rcases p0_3 (m.d 0 5) (by simp) with h477 | h477
            · rcases m.htr 0 1 2 (by decide) (by decide) with h478 | h478
              · rcases m.htr 0 1 3 (by decide) (by decide) with h479 | h479
                · rcases m.htr 0 1 5 (by decide) (by decide) with h480 | h480
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h481 | h481
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h482 | h482
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h483 | h483
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h484 | h484
                          · linarith only [h484, hlam, p0_0]
                          · linarith only [h479, h484, hc13, hc34, hlam, hphi, p0_1]
                        · linarith only [h479, h482, h483, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h473, h482, hlam]
                    · linarith only [h473, h479, h481, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h473, h478, h479, h480, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h473, h478, h479, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h472, h478, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h472, h477, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h476, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h495 | h495
        · linarith only [h495, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h497 | h497
          · rcases p0_3 (m.d 0 5) (by simp) with h498 | h498
            · rcases m.htr 0 1 2 (by decide) (by decide) with h499 | h499
              · rcases m.htr 0 1 3 (by decide) (by decide) with h500 | h500
                · rcases m.htr 0 1 5 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h502 | h502
                    · linarith only [h473, h502, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h504 | h504
                      · linarith only [h498, h501, h502, h504, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                      · linarith only [h499, h502, h504, hc12, hc24, hlam, hphi, p0_1]
                  · linarith only [h472, h500, h501, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h472, h473, h499, h500, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h472, h473, h499, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h472, h498, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h497, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h512 | h512
      · rcases p0_3 (m.d 0 3) (by simp) with h513 | h513
        · linarith only [h513, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h515 | h515
          · rcases p0_3 (m.d 0 5) (by simp) with h516 | h516
            · rcases m.htr 0 1 2 (by decide) (by decide) with h517 | h517
              · linarith only [h472, h517, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h472, h512, h517, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h512, h516, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h515, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h522 | h522
        · linarith only [h522, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h524 | h524
          · rcases p0_3 (m.d 0 5) (by simp) with h525 | h525
            · rcases m.htr 0 1 2 (by decide) (by decide) with h526 | h526
              · linarith only [h472, h526, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h528 | h528
                · linarith only [h472, h528, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
                  · linarith only [h512, h526, h530, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h512, h525, h526, h530, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h525, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h524, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h537 | h537
    · linarith only [h537, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h539 | h539
      · rcases p0_3 (m.d 0 3) (by simp) with h540 | h540
        · rcases p0_3 (m.d 0 4) (by simp) with h541 | h541
          · rcases p0_3 (m.d 0 5) (by simp) with h542 | h542
            · rcases m.htr 0 1 2 (by decide) (by decide) with h543 | h543
              · linarith only [h539, h543, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h543, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h542, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h547 | h547
            · rcases m.htr 0 1 2 (by decide) (by decide) with h548 | h548
              · linarith only [h539, h548, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h548, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h547, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h552 | h552
          · rcases p0_3 (m.d 0 5) (by simp) with h553 | h553
            · rcases m.htr 0 1 2 (by decide) (by decide) with h554 | h554
              · linarith only [h539, h554, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h554, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h553, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h558 | h558
            · rcases m.htr 0 1 2 (by decide) (by decide) with h559 | h559
              · linarith only [h539, h559, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h559, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h558, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h563 | h563
        · rcases p0_3 (m.d 0 4) (by simp) with h564 | h564
          · rcases p0_3 (m.d 0 5) (by simp) with h565 | h565
            · rcases m.htr 0 1 2 (by decide) (by decide) with h566 | h566
              · linarith only [h563, h566, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h566, hlam]
            · linarith only [h565, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h570 | h570
            · rcases m.htr 0 1 2 (by decide) (by decide) with h571 | h571
              · linarith only [h563, h571, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h571, hlam]
            · linarith only [h570, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h575 | h575
          · rcases p0_3 (m.d 0 5) (by simp) with h576 | h576
            · rcases m.htr 0 1 2 (by decide) (by decide) with h577 | h577
              · linarith only [h575, h577, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h577, hlam]
            · linarith only [h576, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h581 | h581
            · rcases m.htr 0 1 2 (by decide) (by decide) with h582 | h582
              · linarith only [h582, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h539, h582, hlam]
            · linarith only [h581, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h586 | h586
    · rcases p0_3 (m.d 0 2) (by simp) with h587 | h587
      · linarith only [h587, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h589 | h589
        · rcases p0_3 (m.d 0 4) (by simp) with h590 | h590
          · rcases p0_3 (m.d 0 5) (by simp) with h591 | h591
            · rcases m.htr 0 1 2 (by decide) (by decide) with h592 | h592
              · rcases m.htr 0 1 3 (by decide) (by decide) with h593 | h593
                · rcases m.htr 0 1 5 (by decide) (by decide) with h594 | h594
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h595 | h595
                    · linarith only [h589, h593, h595, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h589, h595, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h586, h594, hlam]
                · linarith only [h586, h592, h593, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h586, h592, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h591, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h602 | h602
            · rcases m.htr 0 1 2 (by decide) (by decide) with h603 | h603
              · rcases m.htr 0 1 3 (by decide) (by decide) with h604 | h604
                · rcases m.htr 0 1 5 (by decide) (by decide) with h605 | h605
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h606 | h606
                    · linarith only [h589, h604, h606, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h589, h606, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h586, h605, hlam]
                · linarith only [h586, h603, h604, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h586, h603, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h602, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h613 | h613
          · rcases p0_3 (m.d 0 5) (by simp) with h614 | h614
            · rcases m.htr 0 1 2 (by decide) (by decide) with h615 | h615
              · rcases m.htr 0 1 3 (by decide) (by decide) with h616 | h616
                · rcases m.htr 0 1 5 (by decide) (by decide) with h617 | h617
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h618 | h618
                    · linarith only [h617, h618, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h589, h618, hlam]
                  · linarith only [h586, h617, hlam]
                · linarith only [h586, h616, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h586, h615, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h614, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h625 | h625
            · rcases m.htr 0 1 2 (by decide) (by decide) with h626 | h626
              · rcases m.htr 0 1 3 (by decide) (by decide) with h627 | h627
                · rcases m.htr 0 1 5 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h629 | h629
                    · linarith only [h628, h629, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h589, h629, hlam]
                  · linarith only [h586, h628, hlam]
                · linarith only [h586, h627, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h586, h626, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h625, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h636 | h636
      · linarith only [h636, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h638 | h638
        · rcases p0_3 (m.d 0 4) (by simp) with h639 | h639
          · rcases p0_3 (m.d 0 5) (by simp) with h640 | h640
            · rcases m.htr 0 1 2 (by decide) (by decide) with h641 | h641
              · linarith only [h586, h641, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h643 | h643
                · linarith only [h638, h641, h643, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h638, h641, h643, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h640, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h647 | h647
            · rcases m.htr 0 1 2 (by decide) (by decide) with h648 | h648
              · linarith only [h586, h648, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h650 | h650
                · linarith only [h638, h648, h650, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h638, h648, h650, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h647, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h654 | h654
          · rcases p0_3 (m.d 0 5) (by simp) with h655 | h655
            · rcases m.htr 0 1 2 (by decide) (by decide) with h656 | h656
              · linarith only [h586, h656, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h658 | h658
                · linarith only [h654, h656, h658, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h660 | h660
                  · linarith only [h654, h656, h660, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h656, h660, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h655, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h664 | h664
            · rcases m.htr 0 1 2 (by decide) (by decide) with h665 | h665
              · linarith only [h586, h665, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h667 | h667
                · linarith only [h665, h667, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h669 | h669
                  · linarith only [h665, h669, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h665, h669, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h664, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h673 | h673
    · rcases p0_3 (m.d 0 2) (by simp) with h674 | h674
      · rcases p0_3 (m.d 0 3) (by simp) with h675 | h675
        · linarith only [h675, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h677 | h677
          · rcases p0_3 (m.d 0 5) (by simp) with h678 | h678
            · rcases m.htr 0 1 2 (by decide) (by decide) with h679 | h679
              · rcases m.htr 0 1 3 (by decide) (by decide) with h680 | h680
                · rcases m.htr 0 1 5 (by decide) (by decide) with h681 | h681
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h682 | h682
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h683 | h683
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h684 | h684
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h685 | h685
                          · linarith only [h677, h679, h683, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · linarith only [h677, h685, hc03, hc34, hlam, hphi, p0_1]
                        · linarith only [h674, h684, hlam]
                      · linarith only [h674, h680, h683, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h674, h680, h682, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h673, h681, hlam]
                · linarith only [h673, h680, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h673, h679, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h678, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h695 | h695
            · rcases m.htr 0 1 2 (by decide) (by decide) with h696 | h696
              · rcases m.htr 0 1 3 (by decide) (by decide) with h697 | h697
                · rcases m.htr 0 1 5 (by decide) (by decide) with h698 | h698
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h699 | h699
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h700 | h700
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h701 | h701
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h702 | h702
                          · linarith only [h696, h701, h702, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · linarith only [h677, h702, hlam]
                        · linarith only [h674, h701, hlam]
                      · linarith only [h674, h700, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h674, h697, h699, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h673, h698, hlam]
                · linarith only [h673, h697, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h673, h696, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h695, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h712 | h712
        · linarith only [h712, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h714 | h714
          · rcases p0_3 (m.d 0 5) (by simp) with h715 | h715
            · rcases m.htr 0 1 2 (by decide) (by decide) with h716 | h716
              · rcases m.htr 0 1 3 (by decide) (by decide) with h717 | h717
                · rcases m.htr 0 1 5 (by decide) (by decide) with h718 | h718
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h719 | h719
                    · linarith only [h674, h719, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h721 | h721
                      · linarith only [h718, h719, h721, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                      · linarith only [h714, h719, h721, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h673, h718, hlam]
                · linarith only [h673, h717, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h673, h674, h716, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h715, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h728 | h728
            · rcases m.htr 0 1 2 (by decide) (by decide) with h729 | h729
              · rcases m.htr 0 1 3 (by decide) (by decide) with h730 | h730
                · rcases m.htr 0 1 5 (by decide) (by decide) with h731 | h731
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h732 | h732
                    · linarith only [h674, h732, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h734 | h734
                      · linarith only [h731, h732, h734, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h736 | h736
                        · linarith only [h731, h732, h736, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                        · linarith only [h732, h736, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h673, h731, hlam]
                · linarith only [h673, h674, h729, h730, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h673, h674, h729, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h728, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h743 | h743
      · rcases p0_3 (m.d 0 3) (by simp) with h744 | h744
        · linarith only [h744, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h746 | h746
          · rcases p0_3 (m.d 0 5) (by simp) with h747 | h747
            · rcases m.htr 0 1 2 (by decide) (by decide) with h748 | h748
              · linarith only [h673, h743, h748, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h673, h743, h748, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h747, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h752 | h752
            · rcases m.htr 0 1 2 (by decide) (by decide) with h753 | h753
              · linarith only [h673, h743, h753, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h673, h743, h753, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h752, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h757 | h757
        · linarith only [h757, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h759 | h759
          · rcases p0_3 (m.d 0 5) (by simp) with h760 | h760
            · rcases m.htr 0 1 2 (by decide) (by decide) with h761 | h761
              · linarith only [h673, h759, h761, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h763 | h763
                · linarith only [h673, h763, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h765 | h765
                  · linarith only [h743, h759, h761, h765, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h743, h761, h765, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h760, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h769 | h769
            · rcases m.htr 0 1 2 (by decide) (by decide) with h770 | h770
              · linarith only [h673, h770, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h772 | h772
                · linarith only [h673, h772, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h774 | h774
                  · linarith only [h743, h770, h774, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h743, h770, h774, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h769, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h778 | h778
    · rcases p0_3 (m.d 0 2) (by simp) with h779 | h779
      · rcases p0_3 (m.d 0 3) (by simp) with h780 | h780
        · rcases p0_3 (m.d 0 4) (by simp) with h781 | h781
          · linarith only [h781, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h783 | h783
            · rcases m.htr 0 1 2 (by decide) (by decide) with h784 | h784
              · rcases m.htr 0 1 3 (by decide) (by decide) with h785 | h785
                · rcases m.htr 0 1 5 (by decide) (by decide) with h786 | h786
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h787 | h787
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h788 | h788
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h789 | h789
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h791 | h791
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
                              · linarith only [h792, hlam, p0_0]
                              · linarith only [h792, hc04, hc45, hlam, hphi, p0_1]
                            · linarith only [h780, h791, hlam]
                          · linarith only [h780, h788, h790, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                        · linarith only [h779, h789, hlam]
                      · linarith only [h779, h788, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h779, h787, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · linarith only [h778, h786, hlam]
                · linarith only [h778, h785, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h778, h784, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h783, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h804 | h804
          · linarith only [h804, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h806 | h806
            · rcases m.htr 0 1 2 (by decide) (by decide) with h807 | h807
              · rcases m.htr 0 1 3 (by decide) (by decide) with h808 | h808
                · rcases m.htr 0 1 5 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h810 | h810
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h811 | h811
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h812 | h812
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h813 | h813
                          · linarith only [h780, h813, hlam]
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h815 | h815
                            · linarith only [h807, h812, h813, h815, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                            · linarith only [h813, h815, hc03, hc35, hlam, hphi, p0_1]
                        · linarith only [h779, h812, hlam]
                      · linarith only [h779, h811, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h779, h780, h808, h810, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h778, h809, hlam]
                · linarith only [h778, h780, h808, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h778, h780, h807, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h806, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h825 | h825
        · rcases p0_3 (m.d 0 4) (by simp) with h826 | h826
          · linarith only [h826, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h828 | h828
            · rcases m.htr 0 1 2 (by decide) (by decide) with h829 | h829
              · rcases m.htr 0 1 3 (by decide) (by decide) with h830 | h830
                · rcases m.htr 0 1 5 (by decide) (by decide) with h831 | h831
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h832 | h832
                    · linarith only [h779, h825, h830, h832, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h779, h825, h832, hc02, hc23, hlam, hphi, p0_1]
                  · linarith only [h778, h831, hlam]
                · linarith only [h778, h779, h829, h830, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h778, h779, h829, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h828, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h839 | h839
          · linarith only [h839, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h841 | h841
            · rcases m.htr 0 1 2 (by decide) (by decide) with h842 | h842
              · rcases m.htr 0 1 3 (by decide) (by decide) with h843 | h843
                · rcases m.htr 0 1 5 (by decide) (by decide) with h844 | h844
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h845 | h845
                    · linarith only [h779, h844, h845, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h847 | h847
                      · linarith only [h779, h847, hlam]
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h849 | h849
                        · linarith only [h825, h844, h845, h849, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                        · linarith only [h825, h845, h849, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h778, h844, hlam]
                · linarith only [h778, h779, h842, h843, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h778, h779, h842, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h841, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h856 | h856
      · rcases p0_3 (m.d 0 3) (by simp) with h857 | h857
        · rcases p0_3 (m.d 0 4) (by simp) with h858 | h858
          · linarith only [h858, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h860 | h860
            · rcases m.htr 0 1 2 (by decide) (by decide) with h861 | h861
              · linarith only [h778, h856, h861, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h778, h856, h861, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h860, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h865 | h865
          · linarith only [h865, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h867 | h867
            · rcases m.htr 0 1 2 (by decide) (by decide) with h868 | h868
              · linarith only [h778, h856, h868, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h778, h856, h868, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h867, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h872 | h872
        · rcases p0_3 (m.d 0 4) (by simp) with h873 | h873
          · linarith only [h873, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h875 | h875
            · rcases m.htr 0 1 2 (by decide) (by decide) with h876 | h876
              · linarith only [h778, h872, h876, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h878 | h878
                · linarith only [h856, h872, h876, h878, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h856, h872, h876, h878, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h875, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h882 | h882
          · linarith only [h882, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h884 | h884
            · rcases m.htr 0 1 2 (by decide) (by decide) with h885 | h885
              · linarith only [h778, h885, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h887 | h887
                · linarith only [h856, h885, h887, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h889 | h889
                  · linarith only [h856, h885, h889, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h856, h885, h889, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h884, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_H_I_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
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
            · rcases m.htr 0 1 3 (by decide) (by decide) with h8 | h8
              · linarith only [h5, h8, hlam]
              · linarith only [h8, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
            · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
              · linarith only [h13, h5, hlam]
              · linarith only [h13, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 0 5) (by simp) with h18 | h18
            · rcases m.htr 0 1 3 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
                · linarith only [h17, h20, hlam]
                · linarith only [h20, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h19, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h18, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
            · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
              · rcases m.htr 0 1 4 (by decide) (by decide) with h27 | h27
                · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h25, h28, hlam]
                  · linarith only [h28, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h27, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h26, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h25, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h35 | h35
    · rcases p0_3 (m.d 0 2) (by simp) with h36 | h36
      · rcases p0_3 (m.d 0 3) (by simp) with h37 | h37
        · linarith only [h37, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h39 | h39
          · rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
            · rcases m.htr 0 1 3 (by decide) (by decide) with h41 | h41
              · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
                · linarith only [h39, h42, hlam]
                · linarith only [h42, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h41, hlam, p0_0]
            · linarith only [h40, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h47 | h47
            · rcases m.htr 0 1 3 (by decide) (by decide) with h48 | h48
              · rcases m.htr 0 1 4 (by decide) (by decide) with h49 | h49
                · rcases m.htr 0 1 5 (by decide) (by decide) with h50 | h50
                  · linarith only [h47, h50, hlam]
                  · linarith only [h50, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h48, h49, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h48, hlam, p0_0]
            · linarith only [h47, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
          · rcases p0_3 (m.d 0 5) (by simp) with h59 | h59
            · rcases m.htr 0 1 3 (by decide) (by decide) with h60 | h60
              · rcases m.htr 0 1 4 (by decide) (by decide) with h61 | h61
                · linarith only [h58, h61, hlam]
                · linarith only [h36, h61, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h60, hlam, p0_0]
            · linarith only [h59, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · rcases m.htr 0 1 3 (by decide) (by decide) with h67 | h67
              · rcases m.htr 0 1 4 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 1 5 (by decide) (by decide) with h69 | h69
                  · linarith only [h66, h69, hlam]
                  · linarith only [h69, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h36, h68, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h67, hlam, p0_0]
            · linarith only [h66, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h35, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h76 | h76
    · rcases p0_3 (m.d 0 2) (by simp) with h77 | h77
      · rcases p0_3 (m.d 0 3) (by simp) with h78 | h78
        · rcases p0_3 (m.d 0 4) (by simp) with h79 | h79
          · linarith only [h79, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h81 | h81
            · rcases m.htr 0 1 3 (by decide) (by decide) with h82 | h82
              · linarith only [h78, h82, hlam]
              · linarith only [h82, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h81, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h88 | h88
            · rcases m.htr 0 1 3 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 1 4 (by decide) (by decide) with h90 | h90
                · rcases m.htr 0 1 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h88, h91, hlam]
                  · linarith only [h78, h91, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h90, hlam, p0_0]
              · linarith only [h78, h89, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h88, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h97 | h97
        · rcases p0_3 (m.d 0 4) (by simp) with h98 | h98
          · linarith only [h98, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h100 | h100
            · rcases m.htr 0 1 3 (by decide) (by decide) with h101 | h101
              · linarith only [h101, h97, hlam]
              · linarith only [h101, h77, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h100, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · rcases m.htr 0 1 3 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 1 4 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 1 5 (by decide) (by decide) with h110 | h110
                  · linarith only [h107, h110, hlam]
                  · linarith only [h110, h97, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h109, hlam, p0_0]
              · linarith only [h108, h77, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h107, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h76, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h118 | h118
    · linarith only [h118, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h120 | h120
      · rcases p0_3 (m.d 0 3) (by simp) with h121 | h121
        · rcases p0_3 (m.d 0 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 0 5) (by simp) with h123 | h123
            · rcases m.htr 0 1 3 (by decide) (by decide) with h124 | h124
              · linarith only [h124, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h121, h124, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h123, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h128 | h128
            · rcases m.htr 0 1 3 (by decide) (by decide) with h129 | h129
              · linarith only [h129, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h121, h129, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h128, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 3 (by decide) (by decide) with h135 | h135
              · linarith only [h135, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h121, h135, hlam]
            · linarith only [h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h139 | h139
            · rcases m.htr 0 1 3 (by decide) (by decide) with h140 | h140
              · linarith only [h140, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h121, h140, hlam]
            · linarith only [h139, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h120, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h146 | h146
    · rcases p0_3 (m.d 0 2) (by simp) with h147 | h147
      · rcases p0_3 (m.d 0 3) (by simp) with h148 | h148
        · linarith only [h148, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h150 | h150
          · rcases p0_3 (m.d 0 5) (by simp) with h151 | h151
            · rcases m.htr 0 1 3 (by decide) (by decide) with h152 | h152
              · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
                · rcases m.htr 0 1 5 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h155 | h155
                    · linarith only [h150, h155, hlam]
                    · linarith only [h155, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h146, h152, h154, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h146, h152, h153, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h152, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h146, h151, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h162 | h162
            · rcases m.htr 0 1 3 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 1 4 (by decide) (by decide) with h164 | h164
                · rcases m.htr 0 1 5 (by decide) (by decide) with h165 | h165
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h166 | h166
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h167 | h167
                      · linarith only [h162, h167, hlam]
                      · linarith only [h167, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h163, h166, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h146, h163, h165, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h146, h163, h164, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h146, h163, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h146, h162, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h147, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h176 | h176
      · rcases p0_3 (m.d 0 3) (by simp) with h177 | h177
        · linarith only [h177, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h179 | h179
          · rcases p0_3 (m.d 0 5) (by simp) with h180 | h180
            · rcases m.htr 0 1 3 (by decide) (by decide) with h181 | h181
              · linarith only [h146, h181, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h183 | h183
                · linarith only [h181, h183, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h179, h181, h183, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h180, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h187 | h187
            · rcases m.htr 0 1 3 (by decide) (by decide) with h188 | h188
              · linarith only [h146, h188, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h190 | h190
                · linarith only [h188, h190, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h192 | h192
                  · linarith only [h188, h192, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h187, h188, h192, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h187, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h176, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h197 | h197
    · rcases p0_3 (m.d 0 2) (by simp) with h198 | h198
      · rcases p0_3 (m.d 0 3) (by simp) with h199 | h199
        · rcases p0_3 (m.d 0 4) (by simp) with h200 | h200
          · linarith only [h200, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h202 | h202
            · rcases m.htr 0 1 3 (by decide) (by decide) with h203 | h203
              · rcases m.htr 0 1 4 (by decide) (by decide) with h204 | h204
                · rcases m.htr 0 1 5 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h206 | h206
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
                      · linarith only [h202, h207, hlam]
                      · linarith only [h204, h207, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h206, hlam, p0_0]
                  · linarith only [h197, h204, h205, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h199, h203, h204, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h197, h203, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h197, h202, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h215 | h215
          · linarith only [h215, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h217 | h217
            · rcases m.htr 0 1 3 (by decide) (by decide) with h218 | h218
              · rcases m.htr 0 1 4 (by decide) (by decide) with h219 | h219
                · rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h217, h222, hlam]
                      · linarith only [h199, h222, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h221, hlam, p0_0]
                  · linarith only [h197, h199, h218, h220, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h197, h199, h218, h219, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h197, h199, h218, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h197, h217, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h198, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h231 | h231
      · rcases p0_3 (m.d 0 3) (by simp) with h232 | h232
        · rcases p0_3 (m.d 0 4) (by simp) with h233 | h233
          · linarith only [h233, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h235 | h235
            · rcases m.htr 0 1 3 (by decide) (by decide) with h236 | h236
              · linarith only [h197, h236, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h197, h232, h236, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h235, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h240 | h240
          · linarith only [h240, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h242 | h242
            · rcases m.htr 0 1 3 (by decide) (by decide) with h243 | h243
              · linarith only [h197, h243, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h245 | h245
                · linarith only [h197, h245, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h247 | h247
                  · linarith only [h232, h243, h247, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h232, h242, h243, h247, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h242, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h231, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h253 | h253
    · linarith only [h253, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h255 | h255
      · rcases p0_3 (m.d 0 3) (by simp) with h256 | h256
        · rcases p0_3 (m.d 0 4) (by simp) with h257 | h257
          · rcases p0_3 (m.d 0 5) (by simp) with h258 | h258
            · rcases m.htr 0 1 3 (by decide) (by decide) with h259 | h259
              · linarith only [h259, hlam, p0_0]
              · linarith only [h259, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h258, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h263 | h263
            · rcases m.htr 0 1 3 (by decide) (by decide) with h264 | h264
              · linarith only [h264, hlam, p0_0]
              · linarith only [h264, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h263, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h256, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h269 | h269
        · rcases p0_3 (m.d 0 4) (by simp) with h270 | h270
          · rcases p0_3 (m.d 0 5) (by simp) with h271 | h271
            · rcases m.htr 0 1 3 (by decide) (by decide) with h272 | h272
              · linarith only [h272, hlam, p0_0]
              · linarith only [h272, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h271, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h276 | h276
            · rcases m.htr 0 1 3 (by decide) (by decide) with h277 | h277
              · linarith only [h277, hlam, p0_0]
              · linarith only [h277, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h276, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h269, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h282 | h282
    · rcases p0_3 (m.d 0 2) (by simp) with h283 | h283
      · linarith only [h283, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h285 | h285
        · rcases p0_3 (m.d 0 4) (by simp) with h286 | h286
          · rcases p0_3 (m.d 0 5) (by simp) with h287 | h287
            · rcases m.htr 0 1 3 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 1 4 (by decide) (by decide) with h289 | h289
                · rcases m.htr 0 1 5 (by decide) (by decide) with h290 | h290
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h291 | h291
                    · linarith only [h288, h291, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h286, h291, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h288, h290, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h288, h289, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h282, h288, hlam]
            · linarith only [h287, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h298 | h298
            · rcases m.htr 0 1 3 (by decide) (by decide) with h299 | h299
              · rcases m.htr 0 1 4 (by decide) (by decide) with h300 | h300
                · rcases m.htr 0 1 5 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h302 | h302
                    · linarith only [h299, h302, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h286, h302, hlam]
                  · linarith only [h299, h301, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h299, h300, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h282, h299, hlam]
            · linarith only [h298, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h285, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h310 | h310
      · linarith only [h310, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h312 | h312
        · rcases p0_3 (m.d 0 4) (by simp) with h313 | h313
          · rcases p0_3 (m.d 0 5) (by simp) with h314 | h314
            · rcases m.htr 0 1 3 (by decide) (by decide) with h315 | h315
              · linarith only [h282, h315, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h282, h315, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h314, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h319 | h319
            · rcases m.htr 0 1 3 (by decide) (by decide) with h320 | h320
              · linarith only [h282, h320, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h282, h320, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h319, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h312, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h326 | h326
    · rcases p0_3 (m.d 0 2) (by simp) with h327 | h327
      · rcases p0_3 (m.d 0 3) (by simp) with h328 | h328
        · rcases p0_3 (m.d 0 4) (by simp) with h329 | h329
          · linarith only [h329, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h331 | h331
            · rcases m.htr 0 1 3 (by decide) (by decide) with h332 | h332
              · rcases m.htr 0 1 4 (by decide) (by decide) with h333 | h333
                · rcases m.htr 0 1 5 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h335 | h335
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h336 | h336
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h338 | h338
                          · linarith only [h331, h338, hlam]
                          · linarith only [h338, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                        · linarith only [h337, hlam, p0_0]
                      · linarith only [h327, h333, h336, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h327, h333, h335, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · linarith only [h332, h333, h334, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h332, h333, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h326, h332, hlam]
            · linarith only [h327, h331, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h328, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h349 | h349
        · rcases p0_3 (m.d 0 4) (by simp) with h350 | h350
          · linarith only [h350, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h352 | h352
            · rcases m.htr 0 1 3 (by decide) (by decide) with h353 | h353
              · rcases m.htr 0 1 4 (by decide) (by decide) with h354 | h354
                · rcases m.htr 0 1 5 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h356 | h356
                    · linarith only [h327, h356, hlam]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h358 | h358
                      · linarith only [h353, h356, h358, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                      · linarith only [h352, h356, h358, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h353, h355, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h327, h353, h354, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h326, h353, hlam]
            · linarith only [h352, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h349, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h366 | h366
      · rcases p0_3 (m.d 0 3) (by simp) with h367 | h367
        · rcases p0_3 (m.d 0 4) (by simp) with h368 | h368
          · linarith only [h368, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h370 | h370
            · rcases m.htr 0 1 3 (by decide) (by decide) with h371 | h371
              · linarith only [h326, h371, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h326, h371, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h366, h370, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h367, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h376 | h376
        · rcases p0_3 (m.d 0 4) (by simp) with h377 | h377
          · linarith only [h377, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h379 | h379
            · rcases m.htr 0 1 3 (by decide) (by decide) with h380 | h380
              · linarith only [h326, h380, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h326, h380, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h379, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h376, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h386 | h386
    · linarith only [h386, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h388 | h388
      · rcases p0_3 (m.d 0 3) (by simp) with h389 | h389
        · rcases p0_3 (m.d 0 4) (by simp) with h390 | h390
          · rcases p0_3 (m.d 0 5) (by simp) with h391 | h391
            · rcases m.htr 0 1 3 (by decide) (by decide) with h392 | h392
              · linarith only [h392, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h389, h392, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h388, h391, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h390, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h397 | h397
          · rcases p0_3 (m.d 0 5) (by simp) with h398 | h398
            · rcases m.htr 0 1 3 (by decide) (by decide) with h399 | h399
              · linarith only [h399, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h389, h399, hlam]
            · linarith only [h398, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h397, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h404 | h404
        · rcases p0_3 (m.d 0 4) (by simp) with h405 | h405
          · rcases p0_3 (m.d 0 5) (by simp) with h406 | h406
            · rcases m.htr 0 1 3 (by decide) (by decide) with h407 | h407
              · linarith only [h407, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h404, h407, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h404, h406, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h405, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h412 | h412
          · rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
            · rcases m.htr 0 1 3 (by decide) (by decide) with h414 | h414
              · linarith only [h414, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h404, h414, hlam]
            · linarith only [h413, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h412, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h419 | h419
    · rcases p0_3 (m.d 0 2) (by simp) with h420 | h420
      · linarith only [h420, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h422 | h422
        · rcases p0_3 (m.d 0 4) (by simp) with h423 | h423
          · rcases p0_3 (m.d 0 5) (by simp) with h424 | h424
            · rcases m.htr 0 1 3 (by decide) (by decide) with h425 | h425
              · rcases m.htr 0 1 4 (by decide) (by decide) with h426 | h426
                · rcases m.htr 0 1 5 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h428 | h428
                    · linarith only [h428, hlam, p0_0]
                    · linarith only [h428, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h426, h427, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h419, h426, hlam]
              · linarith only [h419, h425, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h419, h424, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h423, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h436 | h436
          · rcases p0_3 (m.d 0 5) (by simp) with h437 | h437
            · rcases m.htr 0 1 3 (by decide) (by decide) with h438 | h438
              · rcases m.htr 0 1 4 (by decide) (by decide) with h439 | h439
                · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h441 | h441
                    · linarith only [h441, hlam, p0_0]
                    · linarith only [h441, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h439, h440, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h419, h439, hlam]
              · linarith only [h419, h438, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h419, h437, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h436, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h449 | h449
      · linarith only [h449, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h451 | h451
        · rcases p0_3 (m.d 0 4) (by simp) with h452 | h452
          · rcases p0_3 (m.d 0 5) (by simp) with h453 | h453
            · rcases m.htr 0 1 3 (by decide) (by decide) with h454 | h454
              · linarith only [h419, h454, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h419, h451, h454, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h451, h453, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h452, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h459 | h459
          · rcases p0_3 (m.d 0 5) (by simp) with h460 | h460
            · rcases m.htr 0 1 3 (by decide) (by decide) with h461 | h461
              · linarith only [h419, h461, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h463 | h463
                · linarith only [h451, h461, h463, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h451, h461, h463, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h460, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h459, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h468 | h468
    · rcases p0_3 (m.d 0 2) (by simp) with h469 | h469
      · rcases p0_3 (m.d 0 3) (by simp) with h470 | h470
        · linarith only [h470, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h472 | h472
          · rcases p0_3 (m.d 0 5) (by simp) with h473 | h473
            · rcases m.htr 0 1 3 (by decide) (by decide) with h474 | h474
              · rcases m.htr 0 1 4 (by decide) (by decide) with h475 | h475
                · rcases m.htr 0 1 5 (by decide) (by decide) with h476 | h476
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h477 | h477
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h479 | h479
                        · linarith only [h479, hlam, p0_0]
                        · linarith only [h474, h479, hc13, hc34, hlam, hphi, p0_1]
                      · linarith only [h474, h477, h478, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                    · linarith only [h469, h477, hlam]
                  · linarith only [h474, h475, h476, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h468, h475, hlam]
              · linarith only [h468, h474, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h468, h473, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h472, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h489 | h489
        · linarith only [h489, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h491 | h491
          · rcases p0_3 (m.d 0 5) (by simp) with h492 | h492
            · rcases m.htr 0 1 3 (by decide) (by decide) with h493 | h493
              · rcases m.htr 0 1 4 (by decide) (by decide) with h494 | h494
                · rcases m.htr 0 1 5 (by decide) (by decide) with h495 | h495
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h496 | h496
                    · linarith only [h469, h494, h496, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h469, h496, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h469, h494, h495, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h468, h494, hlam]
              · linarith only [h468, h469, h493, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h468, h492, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h491, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h504 | h504
      · rcases p0_3 (m.d 0 3) (by simp) with h505 | h505
        · linarith only [h505, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h507 | h507
          · rcases p0_3 (m.d 0 5) (by simp) with h508 | h508
            · rcases m.htr 0 1 3 (by decide) (by decide) with h509 | h509
              · linarith only [h468, h509, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h511 | h511
                · linarith only [h509, h511, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h509, h511, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h508, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h507, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h516 | h516
        · linarith only [h516, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h518 | h518
          · rcases p0_3 (m.d 0 5) (by simp) with h519 | h519
            · rcases m.htr 0 1 3 (by decide) (by decide) with h520 | h520
              · linarith only [h468, h520, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h522 | h522
                · linarith only [h520, h522, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h520, h522, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h519, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h518, hlam, p0_0]
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
    rcases p0_3 (m.d 0 1) (by simp) with h529 | h529
    · linarith only [h529, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h531 | h531
      · rcases p0_3 (m.d 0 3) (by simp) with h532 | h532
        · rcases p0_3 (m.d 0 4) (by simp) with h533 | h533
          · rcases p0_3 (m.d 0 5) (by simp) with h534 | h534
            · rcases m.htr 0 1 3 (by decide) (by decide) with h535 | h535
              · linarith only [h531, h535, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h532, h535, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h534, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h539 | h539
            · rcases m.htr 0 1 3 (by decide) (by decide) with h540 | h540
              · linarith only [h532, h540, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h532, h540, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h539, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h544 | h544
          · rcases p0_3 (m.d 0 5) (by simp) with h545 | h545
            · rcases m.htr 0 1 3 (by decide) (by decide) with h546 | h546
              · linarith only [h544, h546, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h532, h546, hlam]
            · linarith only [h545, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h550 | h550
            · rcases m.htr 0 1 3 (by decide) (by decide) with h551 | h551
              · linarith only [h551, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h532, h551, hlam]
            · linarith only [h550, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h555 | h555
        · rcases p0_3 (m.d 0 4) (by simp) with h556 | h556
          · rcases p0_3 (m.d 0 5) (by simp) with h557 | h557
            · rcases m.htr 0 1 3 (by decide) (by decide) with h558 | h558
              · linarith only [h558, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h555, h558, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h557, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h562 | h562
            · rcases m.htr 0 1 3 (by decide) (by decide) with h563 | h563
              · linarith only [h555, h563, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h555, h563, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h562, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h567 | h567
          · rcases p0_3 (m.d 0 5) (by simp) with h568 | h568
            · rcases m.htr 0 1 3 (by decide) (by decide) with h569 | h569
              · linarith only [h567, h569, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h555, h569, hlam]
            · linarith only [h568, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h573 | h573
            · rcases m.htr 0 1 3 (by decide) (by decide) with h574 | h574
              · linarith only [h574, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h555, h574, hlam]
            · linarith only [h573, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h578 | h578
    · rcases p0_3 (m.d 0 2) (by simp) with h579 | h579
      · linarith only [h579, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h581 | h581
        · rcases p0_3 (m.d 0 4) (by simp) with h582 | h582
          · rcases p0_3 (m.d 0 5) (by simp) with h583 | h583
            · rcases m.htr 0 1 3 (by decide) (by decide) with h584 | h584
              · rcases m.htr 0 1 4 (by decide) (by decide) with h585 | h585
                · rcases m.htr 0 1 5 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h587 | h587
                    · linarith only [h581, h584, h587, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h582, h587, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h578, h586, hlam]
                · linarith only [h578, h585, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h578, h584, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h583, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h594 | h594
            · rcases m.htr 0 1 3 (by decide) (by decide) with h595 | h595
              · rcases m.htr 0 1 4 (by decide) (by decide) with h596 | h596
                · rcases m.htr 0 1 5 (by decide) (by decide) with h597 | h597
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h598 | h598
                    · linarith only [h581, h595, h598, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h582, h598, hlam]
                  · linarith only [h578, h597, hlam]
                · linarith only [h581, h595, h596, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h578, h595, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h594, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h605 | h605
          · rcases p0_3 (m.d 0 5) (by simp) with h606 | h606
            · rcases m.htr 0 1 3 (by decide) (by decide) with h607 | h607
              · rcases m.htr 0 1 4 (by decide) (by decide) with h608 | h608
                · rcases m.htr 0 1 5 (by decide) (by decide) with h609 | h609
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h610 | h610
                    · linarith only [h605, h608, h610, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h605, h610, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h578, h609, hlam]
                · linarith only [h578, h608, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h578, h607, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h606, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h617 | h617
            · rcases m.htr 0 1 3 (by decide) (by decide) with h618 | h618
              · rcases m.htr 0 1 4 (by decide) (by decide) with h619 | h619
                · rcases m.htr 0 1 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h621 | h621
                    · linarith only [h620, h621, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h605, h621, hlam]
                  · linarith only [h578, h620, hlam]
                · linarith only [h578, h619, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h578, h618, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h617, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h628 | h628
      · linarith only [h628, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h630 | h630
        · rcases p0_3 (m.d 0 4) (by simp) with h631 | h631
          · rcases p0_3 (m.d 0 5) (by simp) with h632 | h632
            · rcases m.htr 0 1 3 (by decide) (by decide) with h633 | h633
              · linarith only [h578, h630, h633, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h578, h630, h633, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h632, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h637 | h637
            · rcases m.htr 0 1 3 (by decide) (by decide) with h638 | h638
              · linarith only [h578, h630, h638, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h578, h630, h638, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h637, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h642 | h642
          · rcases p0_3 (m.d 0 5) (by simp) with h643 | h643
            · rcases m.htr 0 1 3 (by decide) (by decide) with h644 | h644
              · linarith only [h578, h642, h644, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h646 | h646
                · linarith only [h630, h642, h644, h646, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h630, h642, h644, h646, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h643, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h650 | h650
            · rcases m.htr 0 1 3 (by decide) (by decide) with h651 | h651
              · linarith only [h578, h651, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h653 | h653
                · linarith only [h630, h651, h653, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h655 | h655
                  · linarith only [h630, h651, h655, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h630, h651, h655, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h650, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h659 | h659
    · rcases p0_3 (m.d 0 2) (by simp) with h660 | h660
      · rcases p0_3 (m.d 0 3) (by simp) with h661 | h661
        · linarith only [h661, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h663 | h663
          · rcases p0_3 (m.d 0 5) (by simp) with h664 | h664
            · rcases m.htr 0 1 3 (by decide) (by decide) with h665 | h665
              · rcases m.htr 0 1 4 (by decide) (by decide) with h666 | h666
                · rcases m.htr 0 1 5 (by decide) (by decide) with h667 | h667
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h668 | h668
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h669 | h669
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h670 | h670
                        · linarith only [h663, h666, h670, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h663, h670, hc03, hc34, hlam, hphi, p0_1]
                      · linarith only [h660, h669, hlam]
                    · linarith only [h660, h665, h668, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h659, h667, hlam]
                · linarith only [h659, h665, h666, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h659, h665, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h664, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h679 | h679
            · rcases m.htr 0 1 3 (by decide) (by decide) with h680 | h680
              · rcases m.htr 0 1 4 (by decide) (by decide) with h681 | h681
                · rcases m.htr 0 1 5 (by decide) (by decide) with h682 | h682
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h683 | h683
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h684 | h684
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h685 | h685
                        · linarith only [h682, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h663, h685, hlam]
                      · linarith only [h660, h684, hlam]
                    · linarith only [h660, h683, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h659, h682, hlam]
                · linarith only [h659, h680, h681, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h659, h680, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h679, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h694 | h694
        · linarith only [h694, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h696 | h696
          · rcases p0_3 (m.d 0 5) (by simp) with h697 | h697
            · rcases m.htr 0 1 3 (by decide) (by decide) with h698 | h698
              · rcases m.htr 0 1 4 (by decide) (by decide) with h699 | h699
                · rcases m.htr 0 1 5 (by decide) (by decide) with h700 | h700
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h701 | h701
                    · linarith only [h660, h696, h699, h701, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h660, h696, h701, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h659, h700, hlam]
                · linarith only [h659, h660, h699, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h659, h660, h698, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h697, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h708 | h708
            · rcases m.htr 0 1 3 (by decide) (by decide) with h709 | h709
              · rcases m.htr 0 1 4 (by decide) (by decide) with h710 | h710
                · rcases m.htr 0 1 5 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h712 | h712
                    · linarith only [h660, h711, h712, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h714 | h714
                      · linarith only [h696, h711, h712, h714, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                      · linarith only [h696, h712, h714, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h659, h711, hlam]
                · linarith only [h659, h710, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h659, h660, h709, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h708, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h721 | h721
      · rcases p0_3 (m.d 0 3) (by simp) with h722 | h722
        · linarith only [h722, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h724 | h724
          · rcases p0_3 (m.d 0 5) (by simp) with h725 | h725
            · rcases m.htr 0 1 3 (by decide) (by decide) with h726 | h726
              · linarith only [h659, h726, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h728 | h728
                · linarith only [h721, h726, h728, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h724, h726, h728, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h725, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h732 | h732
            · rcases m.htr 0 1 3 (by decide) (by decide) with h733 | h733
              · linarith only [h659, h733, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h735 | h735
                · linarith only [h721, h733, h735, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h737 | h737
                  · linarith only [h721, h733, h737, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h733, h737, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h732, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h741 | h741
        · linarith only [h741, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h743 | h743
          · rcases p0_3 (m.d 0 5) (by simp) with h744 | h744
            · rcases m.htr 0 1 3 (by decide) (by decide) with h745 | h745
              · linarith only [h659, h745, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h747 | h747
                · linarith only [h743, h745, h747, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h743, h745, h747, hc01, hc14, hlam, hphi, p0_1]
            · linarith only [h744, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h751 | h751
            · rcases m.htr 0 1 3 (by decide) (by decide) with h752 | h752
              · linarith only [h659, h752, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h754 | h754
                · linarith only [h752, h754, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h756 | h756
                  · linarith only [h752, h756, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h752, h756, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h751, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h760 | h760
    · rcases p0_3 (m.d 0 2) (by simp) with h761 | h761
      · rcases p0_3 (m.d 0 3) (by simp) with h762 | h762
        · rcases p0_3 (m.d 0 4) (by simp) with h763 | h763
          · linarith only [h763, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h765 | h765
            · rcases m.htr 0 1 3 (by decide) (by decide) with h766 | h766
              · rcases m.htr 0 1 4 (by decide) (by decide) with h767 | h767
                · rcases m.htr 0 1 5 (by decide) (by decide) with h768 | h768
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h769 | h769
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h770 | h770
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h771 | h771
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h772 | h772
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h773 | h773
                            · linarith only [h773, hlam, p0_0]
                            · linarith only [h767, h773, hc14, hc45, hlam, hphi, p0_1]
                          · linarith only [h762, h772, hlam]
                        · linarith only [h762, h767, h771, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                      · linarith only [h761, h770, hlam]
                    · linarith only [h761, h767, h769, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · linarith only [h760, h768, hlam]
                · linarith only [h760, h767, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h760, h766, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h765, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h784 | h784
          · linarith only [h784, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h786 | h786
            · rcases m.htr 0 1 3 (by decide) (by decide) with h787 | h787
              · rcases m.htr 0 1 4 (by decide) (by decide) with h788 | h788
                · rcases m.htr 0 1 5 (by decide) (by decide) with h789 | h789
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h790 | h790
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h791 | h791
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h792 | h792
                        · linarith only [h762, h792, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h794 | h794
                          · linarith only [h789, h792, h794, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                          · linarith only [h792, h794, hc03, hc35, hlam, hphi, p0_1]
                      · linarith only [h761, h791, hlam]
                    · linarith only [h761, h762, h787, h790, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · linarith only [h760, h789, hlam]
                · linarith only [h760, h762, h787, h788, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h760, h762, h787, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h786, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h803 | h803
        · rcases p0_3 (m.d 0 4) (by simp) with h804 | h804
          · linarith only [h804, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h806 | h806
            · rcases m.htr 0 1 3 (by decide) (by decide) with h807 | h807
              · rcases m.htr 0 1 4 (by decide) (by decide) with h808 | h808
                · rcases m.htr 0 1 5 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h810 | h810
                    · linarith only [h761, h810, hlam]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h812 | h812
                      · linarith only [h803, h807, h810, h812, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                      · linarith only [h810, h812, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h760, h809, hlam]
                · linarith only [h761, h803, h807, h808, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h760, h761, h807, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h806, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h819 | h819
          · linarith only [h819, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h821 | h821
            · rcases m.htr 0 1 3 (by decide) (by decide) with h822 | h822
              · rcases m.htr 0 1 4 (by decide) (by decide) with h823 | h823
                · rcases m.htr 0 1 5 (by decide) (by decide) with h824 | h824
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h825 | h825
                    · linarith only [h761, h825, hlam]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h827 | h827
                      · linarith only [h824, h825, h827, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi2]
                      · linarith only [h825, h827, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h760, h824, hlam]
                · linarith only [h760, h761, h823, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h760, h761, h822, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h821, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h834 | h834
      · rcases p0_3 (m.d 0 3) (by simp) with h835 | h835
        · rcases p0_3 (m.d 0 4) (by simp) with h836 | h836
          · linarith only [h836, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h838 | h838
            · rcases m.htr 0 1 3 (by decide) (by decide) with h839 | h839
              · linarith only [h760, h834, h839, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h760, h835, h839, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h838, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h843 | h843
          · linarith only [h843, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h845 | h845
            · rcases m.htr 0 1 3 (by decide) (by decide) with h846 | h846
              · linarith only [h760, h846, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h848 | h848
                · linarith only [h760, h848, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h850 | h850
                  · linarith only [h835, h846, h850, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h835, h846, h850, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h845, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h854 | h854
        · rcases p0_3 (m.d 0 4) (by simp) with h855 | h855
          · linarith only [h855, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h857 | h857
            · rcases m.htr 0 1 3 (by decide) (by decide) with h858 | h858
              · linarith only [h760, h858, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h760, h854, h858, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h857, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h862 | h862
          · linarith only [h862, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h864 | h864
            · rcases m.htr 0 1 3 (by decide) (by decide) with h865 | h865
              · linarith only [h760, h865, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h867 | h867
                · linarith only [h760, h867, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h869 | h869
                  · linarith only [h854, h865, h869, hc05, hlam, hphi, ht0b, ht5b, p0_1, u5ehi1]
                  · linarith only [h854, h865, h869, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h864, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_H_I_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1bigk := hb1.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
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
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h5, hlam]
                · linarith only [h10, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h9, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h14 | h14
            · linarith only [h14, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · linarith only [h17, h5, hlam]
                · linarith only [h14, h17, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h16, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 1 5) (by simp) with h22 | h22
            · linarith only [h22, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h21, h26, hlam]
                  · linarith only [h22, h26, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h25, h5, hlam, p0_1]
              · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h31 | h31
            · linarith only [h31, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                          · linarith only [h39, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                          · linarith only [h31, h39, hlam]
                        · linarith only [h21, h38, hlam]
                      · linarith only [h37, h5, hlam]
                    · linarith only [h36, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
                  · linarith only [h31, h35, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h31, h34, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h33, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h49 | h49
    · rcases p0_3 (m.d 1 2) (by simp) with h50 | h50
      · rcases p0_3 (m.d 1 3) (by simp) with h51 | h51
        · linarith only [h51, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
          · rcases p0_3 (m.d 1 5) (by simp) with h54 | h54
            · linarith only [h54, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h56 | h56
              · linarith only [h50, h56, hlam]
              · linarith only [h54, h56, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h59 | h59
            · linarith only [h59, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h61 | h61
              · linarith only [h50, h61, hlam]
              · linarith only [h59, h61, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h64 | h64
        · linarith only [h64, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h66 | h66
          · rcases p0_3 (m.d 1 5) (by simp) with h67 | h67
            · linarith only [h50, h67, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h69 | h69
              · rcases m.htr 0 1 3 (by decide) (by decide) with h70 | h70
                · rcases m.htr 0 1 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h66, h71, hlam]
                  · linarith only [h67, h71, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h70, hlam, p0_0]
              · linarith only [h67, h69, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h76 | h76
            · linarith only [h50, h76, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h78 | h78
              · rcases m.htr 0 1 3 (by decide) (by decide) with h79 | h79
                · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                      · linarith only [h50, h82, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h82, h85, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                          · linarith only [h84, h85, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                          · linarith only [h82, h88, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                              · linarith only [h91, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi8]
                              · linarith only [h76, h91, hlam]
                            · linarith only [h66, h90, hlam]
                    · linarith only [h81, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
                  · linarith only [h76, h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h79, hlam, p0_0]
              · linarith only [h76, h78, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
    · linarith only [h49, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h100 | h100
    · rcases p0_3 (m.d 1 2) (by simp) with h101 | h101
      · rcases p0_3 (m.d 1 3) (by simp) with h102 | h102
        · rcases p0_3 (m.d 1 4) (by simp) with h103 | h103
          · linarith only [h103, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h105 | h105
            · linarith only [h105, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h107 | h107
              · linarith only [h101, h107, hlam]
              · linarith only [h105, h107, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h110 | h110
          · linarith only [h110, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h112 | h112
            · linarith only [h102, h112, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h114 | h114
              · linarith only [h101, h114, hlam]
              · linarith only [h112, h114, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h117 | h117
        · rcases p0_3 (m.d 1 4) (by simp) with h118 | h118
          · linarith only [h118, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h120 | h120
            · linarith only [h101, h120, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h122 | h122
              · rcases m.htr 0 1 3 (by decide) (by decide) with h123 | h123
                · linarith only [h117, h123, hlam]
                · linarith only [h120, h123, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h120, h122, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h129 | h129
            · linarith only [h101, h129, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h131 | h131
              · rcases m.htr 0 1 3 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 1 4 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                        · linarith only [h101, h136, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                          · linarith only [h136, h138, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                          · linarith only [h135, h138, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                        · linarith only [h101, h141, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h143 | h143
                          · linarith only [h141, h143, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                            · linarith only [h117, h145, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                              · linarith only [h145, h147, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi8]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                                · linarith only [h149, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
                                · linarith only [h129, h149, hlam]
                    · linarith only [h134, hc14, hlam, hphi, ht45, p0_1, u5elo1]
                  · linarith only [h133, hlam, p0_0]
                · linarith only [h129, h132, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h129, h131, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
    · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h157 | h157
    · rcases p0_3 (m.d 1 2) (by simp) with h158 | h158
      · rcases p0_3 (m.d 1 3) (by simp) with h159 | h159
        · rcases p0_3 (m.d 1 4) (by simp) with h160 | h160
          · rcases p0_3 (m.d 1 5) (by simp) with h161 | h161
            · linarith only [h161, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h163 | h163
              · linarith only [h158, h163, hlam]
              · linarith only [h163, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h166 | h166
            · linarith only [h166, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h168 | h168
              · linarith only [h158, h168, hlam]
              · linarith only [h168, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 1 5) (by simp) with h172 | h172
            · linarith only [h172, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h174 | h174
              · linarith only [h158, h174, hlam]
              · linarith only [h174, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h177 | h177
            · linarith only [h177, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
              · linarith only [h158, h179, hlam]
              · linarith only [h179, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h182 | h182
        · rcases p0_3 (m.d 1 4) (by simp) with h183 | h183
          · rcases p0_3 (m.d 1 5) (by simp) with h184 | h184
            · linarith only [h184, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h186 | h186
              · rcases m.htr 0 1 3 (by decide) (by decide) with h187 | h187
                · linarith only [h182, h187, hlam]
                · linarith only [h187, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h158, h186, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h191 | h191
            · linarith only [h191, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
              · rcases m.htr 0 1 3 (by decide) (by decide) with h194 | h194
                · linarith only [h182, h194, hlam]
                · linarith only [h194, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h158, h193, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h198 | h198
          · rcases p0_3 (m.d 1 5) (by simp) with h199 | h199
            · linarith only [h199, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h201 | h201
              · rcases m.htr 0 1 3 (by decide) (by decide) with h202 | h202
                · rcases m.htr 0 1 4 (by decide) (by decide) with h203 | h203
                  · linarith only [h198, h203, hlam]
                  · linarith only [h203, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h182, h202, hlam, p0_1]
              · linarith only [h158, h201, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h208 | h208
            · linarith only [h208, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h210 | h210
              · rcases m.htr 0 1 3 (by decide) (by decide) with h211 | h211
                · rcases m.htr 0 1 4 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h214 | h214
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h216 | h216
                          · linarith only [h158, h216, hlam]
                          · linarith only [h214, h216, hc23, hlam, hphi, ht34, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                          · linarith only [h158, h219, hlam]
                          · linarith only [h214, h219, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                          · linarith only [h158, h223, hlam]
                          · linarith only [h222, h223, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                          · linarith only [h158, h226, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                              · linarith only [h182, h229, hlam]
                              · linarith only [h228, h229, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
                              · linarith only [h182, h232, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                                · linarith only [h198, h234, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                                        · linarith only [h214, h228, h234, h236, h239, hc12, hc23, hlam, hphi]
                                        · linarith only [h214, h228, h238, h239, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                                      · linarith only [h222, h238, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                    · linarith only [h214, h237, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                                    · linarith only [h214, h232, h236, h244, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h214, h244, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h213, hlam, p0_0]
                  · linarith only [h212, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h211, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h210, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
    · linarith only [h157, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h252 | h252
    · linarith only [h252, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h254 | h254
      · rcases p0_3 (m.d 1 3) (by simp) with h255 | h255
        · rcases p0_3 (m.d 1 4) (by simp) with h256 | h256
          · rcases p0_3 (m.d 1 5) (by simp) with h257 | h257
            · linarith only [h257, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
              · linarith only [h259, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h261 | h261
                · linarith only [h255, h261, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h263 | h263
                  · linarith only [h256, h263, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h265 | h265
                    · linarith only [h265, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h257, h265, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h268 | h268
            · linarith only [h268, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h270 | h270
              · linarith only [h270, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h272 | h272
                · linarith only [h255, h272, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h275 | h275
                    · linarith only [h275, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h268, h275, hlam]
                  · linarith only [h256, h274, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 1 5) (by simp) with h280 | h280
            · linarith only [h280, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h282 | h282
              · linarith only [h282, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h284 | h284
                · rcases m.htr 0 1 4 (by decide) (by decide) with h285 | h285
                  · linarith only [h279, h285, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h287 | h287
                    · linarith only [h287, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h280, h287, hlam]
                · linarith only [h255, h284, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h291 | h291
            · linarith only [h291, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h293 | h293
              · linarith only [h293, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h295 | h295
                · rcases m.htr 0 1 4 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h297 | h297
                    · linarith only [h297, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h291, h297, hlam]
                  · linarith only [h279, h296, hlam]
                · linarith only [h255, h295, hlam]
      · linarith only [h254, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h304 | h304
    · rcases p0_3 (m.d 1 2) (by simp) with h305 | h305
      · rcases p0_3 (m.d 1 3) (by simp) with h306 | h306
        · linarith only [h306, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h308 | h308
          · rcases p0_3 (m.d 1 5) (by simp) with h309 | h309
            · linarith only [h309, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h311 | h311
              · linarith only [h309, h311, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h304, h311, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h314 | h314
            · linarith only [h314, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h316 | h316
              · linarith only [h314, h316, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h304, h316, hlam]
      · linarith only [h305, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h320 | h320
      · rcases p0_3 (m.d 1 3) (by simp) with h321 | h321
        · linarith only [h321, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h323 | h323
          · rcases p0_3 (m.d 1 5) (by simp) with h324 | h324
            · linarith only [h304, h324, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h326 | h326
              · linarith only [h304, h326, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h328 | h328
                · linarith only [h304, h328, hlam]
                · linarith only [h328, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h331 | h331
            · linarith only [h331, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
              · linarith only [h304, h333, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h335 | h335
                · linarith only [h304, h335, hlam]
                · linarith only [h335, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h320, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h339 | h339
    · rcases p0_3 (m.d 1 2) (by simp) with h340 | h340
      · rcases p0_3 (m.d 1 3) (by simp) with h341 | h341
        · rcases p0_3 (m.d 1 4) (by simp) with h342 | h342
          · linarith only [h342, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h344 | h344
            · linarith only [h344, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h346 | h346
              · linarith only [h344, h346, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h339, h346, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h349 | h349
          · linarith only [h349, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h351 | h351
            · linarith only [h341, h351, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h353 | h353
              · linarith only [h351, h353, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h339, h353, hlam]
      · linarith only [h340, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h357 | h357
      · rcases p0_3 (m.d 1 3) (by simp) with h358 | h358
        · rcases p0_3 (m.d 1 4) (by simp) with h359 | h359
          · linarith only [h359, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h361 | h361
            · linarith only [h339, h361, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h363 | h363
              · linarith only [h339, h363, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h365 | h365
                · linarith only [h339, h358, h365, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h367 | h367
                  · linarith only [h339, h367, hlam]
                  · linarith only [h367, hc01, hc12, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h370 | h370
          · linarith only [h370, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h372 | h372
            · linarith only [h358, h372, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
              · linarith only [h372, h374, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h376 | h376
                · rcases m.htr 0 1 4 (by decide) (by decide) with h377 | h377
                  · linarith only [h339, h377, hlam]
                  · linarith only [h376, h377, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h358, h376, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h357, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h382 | h382
    · rcases p0_3 (m.d 1 2) (by simp) with h383 | h383
      · rcases p0_3 (m.d 1 3) (by simp) with h384 | h384
        · rcases p0_3 (m.d 1 4) (by simp) with h385 | h385
          · rcases p0_3 (m.d 1 5) (by simp) with h386 | h386
            · linarith only [h386, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h388 | h388
              · linarith only [h388, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h382, h388, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h391 | h391
            · linarith only [h391, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h393 | h393
              · linarith only [h393, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h382, h393, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h396 | h396
          · rcases p0_3 (m.d 1 5) (by simp) with h397 | h397
            · linarith only [h397, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h399 | h399
              · linarith only [h399, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h382, h399, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h402 | h402
            · linarith only [h402, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h404 | h404
              · linarith only [h404, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h382, h404, hlam]
      · linarith only [h383, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h408 | h408
      · rcases p0_3 (m.d 1 3) (by simp) with h409 | h409
        · rcases p0_3 (m.d 1 4) (by simp) with h410 | h410
          · rcases p0_3 (m.d 1 5) (by simp) with h411 | h411
            · linarith only [h411, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h413 | h413
              · linarith only [h382, h413, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h415 | h415
                · linarith only [h382, h409, h415, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h417 | h417
                  · linarith only [h382, h410, h417, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h419 | h419
                    · linarith only [h382, h419, hlam]
                    · linarith only [h419, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h422 | h422
            · linarith only [h422, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h424 | h424
              · linarith only [h424, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h426 | h426
                · linarith only [h382, h409, h426, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h428 | h428
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h429 | h429
                    · linarith only [h382, h429, hlam]
                    · linarith only [h428, h429, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h410, h428, hc01, hc12, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h433 | h433
          · rcases p0_3 (m.d 1 5) (by simp) with h434 | h434
            · linarith only [h434, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h436 | h436
              · linarith only [h436, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h438 | h438
                · rcases m.htr 0 1 4 (by decide) (by decide) with h439 | h439
                  · linarith only [h382, h433, h439, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h441 | h441
                    · linarith only [h382, h441, hlam]
                    · linarith only [h438, h441, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h409, h438, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h445 | h445
            · linarith only [h445, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h447 | h447
              · linarith only [h447, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h449 | h449
                · rcases m.htr 0 1 4 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h451 | h451
                    · linarith only [h382, h451, hlam]
                    · linarith only [h449, h451, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h433, h449, h450, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h409, h449, hc01, hc12, hlam, hphi, p0_1]
      · linarith only [h408, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h457 | h457
    · linarith only [h457, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h459 | h459
      · rcases p0_3 (m.d 1 3) (by simp) with h460 | h460
        · rcases p0_3 (m.d 1 4) (by simp) with h461 | h461
          · rcases p0_3 (m.d 1 5) (by simp) with h462 | h462
            · linarith only [h462, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h464 | h464
              · linarith only [h459, h464, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h466 | h466
                · linarith only [h466, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h468 | h468
                  · linarith only [h461, h468, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h470 | h470
                    · linarith only [h459, h470, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h462, h470, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h473 | h473
            · linarith only [h473, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h475 | h475
              · linarith only [h459, h475, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h477 | h477
                · linarith only [h477, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h479 | h479
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h480 | h480
                    · linarith only [h459, h480, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h473, h480, hlam]
                  · linarith only [h461, h479, hlam]
        · linarith only [h460, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h485 | h485
        · rcases p0_3 (m.d 1 4) (by simp) with h486 | h486
          · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
            · linarith only [h487, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
              · rcases m.htr 0 1 3 (by decide) (by decide) with h490 | h490
                · linarith only [h490, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h492 | h492
                  · linarith only [h486, h492, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h494 | h494
                    · linarith only [h494, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h487, h494, hlam]
              · linarith only [h459, h489, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h498 | h498
            · linarith only [h498, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h500 | h500
              · rcases m.htr 0 1 3 (by decide) (by decide) with h501 | h501
                · linarith only [h501, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h503 | h503
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h504 | h504
                    · linarith only [h504, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h498, h504, hlam]
                  · linarith only [h486, h503, hlam]
              · linarith only [h459, h500, hlam]
        · linarith only [h485, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h510 | h510
    · rcases p0_3 (m.d 1 2) (by simp) with h511 | h511
      · linarith only [h511, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h513 | h513
        · rcases p0_3 (m.d 1 4) (by simp) with h514 | h514
          · rcases p0_3 (m.d 1 5) (by simp) with h515 | h515
            · linarith only [h515, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h517 | h517
              · rcases m.htr 0 1 3 (by decide) (by decide) with h518 | h518
                · linarith only [h515, h518, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h510, h518, hlam]
              · linarith only [h517, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h522 | h522
            · linarith only [h522, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h524 | h524
              · rcases m.htr 0 1 3 (by decide) (by decide) with h525 | h525
                · linarith only [h522, h525, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h510, h525, hlam]
              · linarith only [h524, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h513, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h530 | h530
      · linarith only [h530, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h532 | h532
        · rcases p0_3 (m.d 1 4) (by simp) with h533 | h533
          · rcases p0_3 (m.d 1 5) (by simp) with h534 | h534
            · linarith only [h534, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h536 | h536
              · linarith only [h510, h536, hlam]
              · linarith only [h536, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h539 | h539
            · linarith only [h539, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h541 | h541
              · linarith only [h510, h541, hlam]
              · linarith only [h541, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h532, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h546 | h546
    · rcases p0_3 (m.d 1 2) (by simp) with h547 | h547
      · rcases p0_3 (m.d 1 3) (by simp) with h548 | h548
        · rcases p0_3 (m.d 1 4) (by simp) with h549 | h549
          · linarith only [h549, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h551 | h551
            · linarith only [h551, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h553 | h553
              · linarith only [h547, h551, h553, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h546, h551, h553, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · linarith only [h548, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h557 | h557
        · rcases p0_3 (m.d 1 4) (by simp) with h558 | h558
          · linarith only [h558, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h560 | h560
            · linarith only [h547, h560, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h562 | h562
              · rcases m.htr 0 1 3 (by decide) (by decide) with h563 | h563
                · linarith only [h560, h563, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h546, h563, hlam]
              · linarith only [h546, h560, h562, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · linarith only [h557, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h568 | h568
      · rcases p0_3 (m.d 1 3) (by simp) with h569 | h569
        · rcases p0_3 (m.d 1 4) (by simp) with h570 | h570
          · linarith only [h570, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h572 | h572
            · linarith only [h546, h572, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h574 | h574
              · linarith only [h546, h568, h574, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h576 | h576
                · linarith only [h546, h576, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h578 | h578
                  · linarith only [h546, h578, hlam]
                  · linarith only [h568, h578, hc01, hc12, hlam, hphi, p0_1]
        · linarith only [h569, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h582 | h582
        · rcases p0_3 (m.d 1 4) (by simp) with h583 | h583
          · linarith only [h583, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h585 | h585
            · linarith only [h568, h585, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h587 | h587
              · rcases m.htr 0 1 3 (by decide) (by decide) with h588 | h588
                · linarith only [h546, h588, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h590 | h590
                  · linarith only [h546, h590, hlam]
                  · linarith only [h587, h590, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h568, h587, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h582, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h595 | h595
    · rcases p0_3 (m.d 1 2) (by simp) with h596 | h596
      · rcases p0_3 (m.d 1 3) (by simp) with h597 | h597
        · rcases p0_3 (m.d 1 4) (by simp) with h598 | h598
          · rcases p0_3 (m.d 1 5) (by simp) with h599 | h599
            · linarith only [h599, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h601 | h601
              · linarith only [h596, h601, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h595, h601, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h604 | h604
            · linarith only [h604, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h606 | h606
              · linarith only [h596, h606, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h595, h606, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · linarith only [h597, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h610 | h610
        · rcases p0_3 (m.d 1 4) (by simp) with h611 | h611
          · rcases p0_3 (m.d 1 5) (by simp) with h612 | h612
            · linarith only [h612, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h614 | h614
              · rcases m.htr 0 1 3 (by decide) (by decide) with h615 | h615
                · linarith only [h615, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h595, h615, hlam]
              · linarith only [h596, h614, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h619 | h619
            · linarith only [h619, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h621 | h621
              · rcases m.htr 0 1 3 (by decide) (by decide) with h622 | h622
                · linarith only [h622, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h595, h622, hlam]
              · linarith only [h596, h621, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h610, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h627 | h627
      · rcases p0_3 (m.d 1 3) (by simp) with h628 | h628
        · rcases p0_3 (m.d 1 4) (by simp) with h629 | h629
          · rcases p0_3 (m.d 1 5) (by simp) with h630 | h630
            · linarith only [h630, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h632 | h632
              · linarith only [h627, h632, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h634 | h634
                · linarith only [h595, h634, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h636 | h636
                  · linarith only [h595, h629, h636, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h638 | h638
                    · linarith only [h595, h638, hlam]
                    · linarith only [h627, h638, hc01, hc12, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h641 | h641
            · linarith only [h641, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h643 | h643
              · linarith only [h627, h643, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h645 | h645
                · linarith only [h595, h645, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h647 | h647
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h648 | h648
                    · linarith only [h595, h648, hlam]
                    · linarith only [h627, h647, h648, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h627, h629, h647, hc01, hc12, hlam, hphi, p0_1]
        · linarith only [h628, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h653 | h653
        · rcases p0_3 (m.d 1 4) (by simp) with h654 | h654
          · rcases p0_3 (m.d 1 5) (by simp) with h655 | h655
            · linarith only [h655, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h657 | h657
              · rcases m.htr 0 1 3 (by decide) (by decide) with h658 | h658
                · linarith only [h658, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h660 | h660
                  · linarith only [h595, h654, h660, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h662 | h662
                    · linarith only [h595, h662, hlam]
                    · linarith only [h657, h662, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h627, h657, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h666 | h666
            · linarith only [h666, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h668 | h668
              · rcases m.htr 0 1 3 (by decide) (by decide) with h669 | h669
                · linarith only [h595, h669, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h671 | h671
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h672 | h672
                    · linarith only [h595, h672, hlam]
                    · linarith only [h672, hc01, hc13, hlam, hphi, p0_1]
                  · linarith only [h654, h668, h671, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h627, h668, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h653, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h678 | h678
    · linarith only [h678, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h680 | h680
      · rcases p0_3 (m.d 1 3) (by simp) with h681 | h681
        · rcases p0_3 (m.d 1 4) (by simp) with h682 | h682
          · rcases p0_3 (m.d 1 5) (by simp) with h683 | h683
            · linarith only [h683, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h685 | h685
              · linarith only [h680, h685, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h687 | h687
                · linarith only [h681, h687, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h689 | h689
                  · linarith only [h689, hlam, p0_0]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h691 | h691
                    · linarith only [h680, h691, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h683, h691, hlam]
          · linarith only [h682, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h695 | h695
          · rcases p0_3 (m.d 1 5) (by simp) with h696 | h696
            · linarith only [h696, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h698 | h698
              · linarith only [h680, h698, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h700 | h700
                · rcases m.htr 0 1 4 (by decide) (by decide) with h701 | h701
                  · linarith only [h701, hlam, p0_0]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h703 | h703
                    · linarith only [h680, h703, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h696, h703, hlam]
                · linarith only [h681, h700, hlam]
          · linarith only [h695, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h708 | h708
        · rcases p0_3 (m.d 1 4) (by simp) with h709 | h709
          · rcases p0_3 (m.d 1 5) (by simp) with h710 | h710
            · linarith only [h710, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h712 | h712
              · rcases m.htr 0 1 3 (by decide) (by decide) with h713 | h713
                · linarith only [h708, h713, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h715 | h715
                  · linarith only [h715, hlam, p0_0]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h717 | h717
                    · linarith only [h708, h717, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h710, h717, hlam]
              · linarith only [h680, h712, hlam]
          · linarith only [h709, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h722 | h722
          · rcases p0_3 (m.d 1 5) (by simp) with h723 | h723
            · linarith only [h723, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h725 | h725
              · rcases m.htr 0 1 3 (by decide) (by decide) with h726 | h726
                · rcases m.htr 0 1 4 (by decide) (by decide) with h727 | h727
                  · linarith only [h727, hlam, p0_0]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h729 | h729
                    · linarith only [h729, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                    · linarith only [h723, h729, hlam]
                · linarith only [h708, h726, hlam]
              · linarith only [h680, h725, hlam]
          · linarith only [h722, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h735 | h735
    · rcases p0_3 (m.d 1 2) (by simp) with h736 | h736
      · linarith only [h736, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h738 | h738
        · rcases p0_3 (m.d 1 4) (by simp) with h739 | h739
          · rcases p0_3 (m.d 1 5) (by simp) with h740 | h740
            · linarith only [h740, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h742 | h742
              · rcases m.htr 0 1 3 (by decide) (by decide) with h743 | h743
                · linarith only [h738, h740, h743, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h735, h740, h743, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h735, h742, hlam, p0_1]
          · linarith only [h739, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h748 | h748
          · rcases p0_3 (m.d 1 5) (by simp) with h749 | h749
            · linarith only [h749, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h751 | h751
              · rcases m.htr 0 1 3 (by decide) (by decide) with h752 | h752
                · rcases m.htr 0 1 4 (by decide) (by decide) with h753 | h753
                  · linarith only [h749, h753, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                  · linarith only [h735, h753, hlam]
                · linarith only [h738, h752, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h735, h751, hlam, p0_1]
          · linarith only [h748, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h759 | h759
      · linarith only [h759, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h761 | h761
        · rcases p0_3 (m.d 1 4) (by simp) with h762 | h762
          · rcases p0_3 (m.d 1 5) (by simp) with h763 | h763
            · linarith only [h735, h763, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h765 | h765
              · linarith only [h735, h765, hlam]
              · linarith only [h761, h765, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h762, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h769 | h769
          · rcases p0_3 (m.d 1 5) (by simp) with h770 | h770
            · linarith only [h770, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h772 | h772
              · linarith only [h735, h772, hlam]
              · linarith only [h772, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h769, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h776 | h776
    · rcases p0_3 (m.d 1 2) (by simp) with h777 | h777
      · rcases p0_3 (m.d 1 3) (by simp) with h778 | h778
        · linarith only [h778, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h780 | h780
          · rcases p0_3 (m.d 1 5) (by simp) with h781 | h781
            · linarith only [h781, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h783 | h783
              · linarith only [h777, h781, h783, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h776, h781, h783, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · linarith only [h780, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h787 | h787
        · linarith only [h787, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h789 | h789
          · rcases p0_3 (m.d 1 5) (by simp) with h790 | h790
            · linarith only [h777, h790, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h792 | h792
              · rcases m.htr 0 1 3 (by decide) (by decide) with h793 | h793
                · rcases m.htr 0 1 4 (by decide) (by decide) with h794 | h794
                  · linarith only [h790, h794, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                  · linarith only [h776, h794, hlam]
                · linarith only [h793, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h776, h777, h792, hlam, p0_1]
          · linarith only [h789, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h800 | h800
      · rcases p0_3 (m.d 1 3) (by simp) with h801 | h801
        · linarith only [h801, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h803 | h803
          · rcases p0_3 (m.d 1 5) (by simp) with h804 | h804
            · linarith only [h776, h804, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h806 | h806
              · linarith only [h776, h800, h806, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h808 | h808
                · linarith only [h776, h808, hlam]
                · linarith only [h800, h808, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h803, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h812 | h812
        · linarith only [h812, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h814 | h814
          · rcases p0_3 (m.d 1 5) (by simp) with h815 | h815
            · linarith only [h800, h815, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h817 | h817
              · rcases m.htr 0 1 3 (by decide) (by decide) with h818 | h818
                · linarith only [h776, h818, hlam]
                · linarith only [h817, h818, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h800, h817, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h814, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h824 | h824
    · rcases p0_3 (m.d 1 2) (by simp) with h825 | h825
      · rcases p0_3 (m.d 1 3) (by simp) with h826 | h826
        · rcases p0_3 (m.d 1 4) (by simp) with h827 | h827
          · rcases p0_3 (m.d 1 5) (by simp) with h828 | h828
            · linarith only [h828, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h830 | h830
              · linarith only [h825, h830, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h824, h830, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · linarith only [h827, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h834 | h834
          · rcases p0_3 (m.d 1 5) (by simp) with h835 | h835
            · linarith only [h835, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h837 | h837
              · linarith only [h825, h837, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h824, h837, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · linarith only [h834, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h841 | h841
        · rcases p0_3 (m.d 1 4) (by simp) with h842 | h842
          · rcases p0_3 (m.d 1 5) (by simp) with h843 | h843
            · linarith only [h843, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h845 | h845
              · rcases m.htr 0 1 3 (by decide) (by decide) with h846 | h846
                · linarith only [h841, h846, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h824, h846, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h824, h825, h845, hlam, p0_1]
          · linarith only [h842, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h851 | h851
          · rcases p0_3 (m.d 1 5) (by simp) with h852 | h852
            · linarith only [h852, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h854 | h854
              · rcases m.htr 0 1 3 (by decide) (by decide) with h855 | h855
                · rcases m.htr 0 1 4 (by decide) (by decide) with h856 | h856
                  · linarith only [h856, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                  · linarith only [h824, h856, hlam]
                · linarith only [h841, h855, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h824, h825, h854, hlam, p0_1]
          · linarith only [h851, hlam, p0_0]
    · rcases p0_3 (m.d 1 2) (by simp) with h862 | h862
      · rcases p0_3 (m.d 1 3) (by simp) with h863 | h863
        · rcases p0_3 (m.d 1 4) (by simp) with h864 | h864
          · rcases p0_3 (m.d 1 5) (by simp) with h865 | h865
            · linarith only [h865, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h867 | h867
              · linarith only [h824, h862, h867, hlam, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h869 | h869
                · linarith only [h824, h863, h869, hlam, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h871 | h871
                  · linarith only [h824, h871, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h873 | h873
                    · linarith only [h824, h873, hlam]
                    · linarith only [h873, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h864, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h877 | h877
          · rcases p0_3 (m.d 1 5) (by simp) with h878 | h878
            · linarith only [h878, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h880 | h880
              · linarith only [h862, h880, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h882 | h882
                · rcases m.htr 0 1 4 (by decide) (by decide) with h883 | h883
                  · linarith only [h824, h883, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h885 | h885
                    · linarith only [h824, h885, hlam]
                    · linarith only [h862, h882, h885, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h862, h863, h882, hc01, hc12, hlam, hphi, p0_1]
          · linarith only [h877, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h890 | h890
        · rcases p0_3 (m.d 1 4) (by simp) with h891 | h891
          · rcases p0_3 (m.d 1 5) (by simp) with h892 | h892
            · linarith only [h892, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h894 | h894
              · rcases m.htr 0 1 3 (by decide) (by decide) with h895 | h895
                · linarith only [h890, h895, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h897 | h897
                  · linarith only [h824, h897, hlam, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h899 | h899
                    · linarith only [h824, h899, hlam]
                    · linarith only [h890, h894, h899, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h862, h890, h894, hc01, hc13, hlam, hphi, p0_1]
          · linarith only [h891, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h904 | h904
          · rcases p0_3 (m.d 1 5) (by simp) with h905 | h905
            · linarith only [h905, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h907 | h907
              · rcases m.htr 0 1 3 (by decide) (by decide) with h908 | h908
                · rcases m.htr 0 1 4 (by decide) (by decide) with h909 | h909
                  · linarith only [h909, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h911 | h911
                    · linarith only [h824, h911, hlam]
                    · linarith only [h911, hc01, hc14, hlam, hphi, p0_1]
                · linarith only [h890, h907, h908, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h862, h907, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h904, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h13 | h13
              · linarith only [h13, h4, h5, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                · linarith only [h0, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h15, h2, h4, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 0 3 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h20, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                  · linarith only [h1, h20, h22, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h18, h22, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h18, h19, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h26 | h26
              · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h27, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h18, h29, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h1, h27, h31, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h31, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h34, h4, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                  · linarith only [h0, h18, h36, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h1, h34, h38, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h38, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h42 | h42
        · rcases m.htr 0 2 3 (by decide) (by decide) with h43 | h43
          · rcases m.htr 0 2 4 (by decide) (by decide) with h44 | h44
            · linarith only [h0, h2, h44, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h46 | h46
              · linarith only [h1, h2, h46, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                · linarith only [h0, h48, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h2, h43, h48, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h51 | h51
            · linarith only [h1, h2, h43, h51, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h53 | h53
              · linarith only [h1, h2, h53, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h2, h43, h55, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                  · linarith only [h0, h2, h42, h51, h57, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h1, h55, h59, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h59, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h42, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h63 | h63
      · rcases m.htr 0 1 5 (by decide) (by decide) with h64 | h64
        · rcases m.htr 0 2 3 (by decide) (by decide) with h65 | h65
          · linarith only [h0, h1, h65, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h67 | h67
            · rcases m.htr 0 3 4 (by decide) (by decide) with h68 | h68
              · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                · linarith only [h0, h65, h67, h69, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h0, h1, h71, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h67, h71, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1, h63, h68, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                · linarith only [h0, h1, h65, h76, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                  · linarith only [h0, h1, h67, h78, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h1, h63, h78, h80, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h80, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h1, h63, h75, hlam]
        · linarith only [h64, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h85 | h85
        · rcases m.htr 0 2 3 (by decide) (by decide) with h86 | h86
          · linarith only [h0, h1, h86, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h88 | h88
            · linarith only [h0, h63, h88, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                · linarith only [h0, h86, h91, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
                  · linarith only [h0, h63, h85, h88, h93, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                    · linarith only [h0, h95, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h95, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                · linarith only [h0, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                  · linarith only [h0, h100, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                    · linarith only [h0, h102, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h102, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h85, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h106 | h106
    · rcases m.htr 0 1 4 (by decide) (by decide) with h107 | h107
      · rcases m.htr 0 1 5 (by decide) (by decide) with h108 | h108
        · rcases m.htr 0 2 3 (by decide) (by decide) with h109 | h109
          · rcases m.htr 0 2 4 (by decide) (by decide) with h110 | h110
            · rcases m.htr 0 3 4 (by decide) (by decide) with h111 | h111
              · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                      · linarith only [h106, h115, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h111, h115, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h114, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h106, h110, h112, h113, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h106, h109, h112, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                      · linarith only [h106, h111, h124, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                        · linarith only [h0, h106, h126, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h126, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h123, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h106, h110, h121, h122, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h109, h121, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h107, h110, hlam]
          · linarith only [h0, h106, h109, hlam]
        · linarith only [h108, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h135 | h135
        · rcases m.htr 0 2 3 (by decide) (by decide) with h136 | h136
          · rcases m.htr 0 2 4 (by decide) (by decide) with h137 | h137
            · rcases m.htr 0 3 4 (by decide) (by decide) with h138 | h138
              · linarith only [h106, h107, h138, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                      · linarith only [h106, h107, h137, h138, h143, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                        · linarith only [h106, h107, h137, h145, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h145, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h107, h141, h142, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h137, h141, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h136, h140, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
              · linarith only [h0, h106, h137, h151, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                      · linarith only [h0, h106, h137, h151, h156, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h0, h106, h137, h158, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h158, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h137, h154, h155, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                      · linarith only [h106, h163, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h165 | h165
                        · linarith only [h106, h165, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h153, h165, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h106, h153, h162, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h0, h106, h136, h153, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h106, h136, hlam]
        · linarith only [h106, h135, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h172 | h172
      · rcases m.htr 0 1 5 (by decide) (by decide) with h173 | h173
        · rcases m.htr 0 2 3 (by decide) (by decide) with h174 | h174
          · rcases m.htr 0 2 4 (by decide) (by decide) with h175 | h175
            · rcases m.htr 0 3 4 (by decide) (by decide) with h176 | h176
              · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h179 | h179
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                          · linarith only [h172, h182, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h182, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h106, h172, h178, h181, hc24, hlam, hphi, ht45, u5elo3]
                      · linarith only [h106, h172, h174, h176, h178, h180, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h106, h172, h177, h178, h179, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h106, h175, h177, h178, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h174, h177, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h106, h172, h176, hlam]
            · linarith only [h0, h172, h175, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h192 | h192
            · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
              · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
                          · linarith only [h0, h172, h174, h194, h199, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h199, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h174, h194, h198, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h172, h174, h193, h194, h195, h197, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h196, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h174, h194, h195, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h209 | h209
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                          · linarith only [h0, h172, h174, h210, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h210, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h209, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h193, h194, h208, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h172, h206, h207, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h172, h174, h192, h206, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h0, h172, h174, h193, hlam]
            · linarith only [h0, h172, h192, hlam]
        · linarith only [h173, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
        · rcases m.htr 0 2 3 (by decide) (by decide) with h221 | h221
          · rcases m.htr 0 2 4 (by decide) (by decide) with h222 | h222
            · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
              · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                            · linarith only [h221, h230, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h221, h223, h230, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h172, h220, h226, h229, hc25, hlam, hphi, u5elo4]
                        · linarith only [h172, h220, h226, h227, h228, hc25, hlam, hphi, u5elo3]
                      · linarith only [h221, h223, h227, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h106, h224, h226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h106, h220, h222, h224, h225, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h221, h224, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                            · linarith only [h106, h220, h221, h223, h241, h245, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h247 | h247
                              · linarith only [h222, h245, h247, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h247, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h106, h220, h223, h241, h242, h244, hc25, hlam, hphi, u5elo4]
                        · linarith only [h106, h220, h223, h241, h242, h243, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h253 | h253
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                            · linarith only [h106, h220, h241, h242, h254, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                              · linarith only [h222, h254, h256, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h256, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h106, h220, h241, h242, h253, hc25, hlam, hphi, u5elo4]
                        · linarith only [h106, h220, h241, h252, hc25, hlam, hphi, u5elo3]
                    · linarith only [h241, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h106, h222, h239, h240, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h221, h239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h264 | h264
              · linarith only [h221, h222, h264, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h270 | h270
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h271 | h271
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                            · linarith only [h221, h222, h264, h272, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h274 | h274
                              · linarith only [h221, h222, h266, h269, h272, h274, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h274, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h271, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h270, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                            · linarith only [h106, h220, h268, h269, h281, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                              · linarith only [h221, h222, h283, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h283, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h222, h267, h280, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h106, h220, h268, h279, hc25, hlam, hphi, u5elo3]
                    · linarith only [h268, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                      · linarith only [h106, h264, h266, h267, h290, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                            · linarith only [h221, h290, h294, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                              · linarith only [h221, h222, h296, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h296, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h106, h220, h266, h267, h289, h293, hc25, hlam, hphi, u5elo4]
                        · linarith only [h106, h220, h289, h292, hc25, hlam, hphi, u5elo3]
                    · linarith only [h106, h266, h289, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h220, h221, h266, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h303 | h303
            · rcases m.htr 0 3 4 (by decide) (by decide) with h304 | h304
              · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h309 | h309
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h313 | h313
                                · linarith only [h221, h303, h313, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h313, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h221, h312, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h172, h221, h303, h304, h311, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h310, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h172, h220, h221, h303, h305, h307, h309, hc25, hlam, hphi, u5elo3]
                      · linarith only [h172, h220, h221, h303, h304, h305, h307, h308, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h221, h303, h305, h307, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h221, h303, h305, h306, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h325 | h325
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h326 | h326
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h327 | h327
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h328 | h328
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h329 | h329
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h330 | h330
                                · linarith only [h303, h330, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h330, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h172, h220, h305, h323, h324, h329, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h172, h220, h305, h323, h324, h328, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h172, h220, h324, h327, hc25, hlam, hphi, u5elo4]
                        · linarith only [h326, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h172, h220, h304, h305, h323, h324, h325, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h172, h323, h324, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h221, h303, h323, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h221, h303, h304, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h341 | h341
              · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
                · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h349 | h349
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h351 | h351
                                  · linarith only [h341, h351, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h351, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h220, h303, h347, h350, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h349, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h221, h341, h348, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h220, h303, h343, h346, h347, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h303, h343, h345, h346, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h341, h345, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h344, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h220, h221, h342, h343, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h362 | h362
                  · linarith only [h0, h220, h303, h342, h362, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h365 | h365
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h367 | h367
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h369 | h369
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h370 | h370
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h371 | h371
                                  · linarith only [h341, h371, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h371, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h220, h362, h367, h370, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h0, h362, h368, h369, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h221, h341, h368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h220, h362, h364, h367, hc25, hlam, hphi, u5elo4]
                        · linarith only [h0, h220, h362, h364, h365, h366, hc25, hlam, hphi, u5elo3]
                      · linarith only [h341, h365, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h364, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
                · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h385 | h385
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h386 | h386
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h387 | h387
                            · linarith only [h106, h220, h341, h381, h383, h387, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h220, h221, h381, h383, h384, h387, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h386, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h385, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h392 | h392
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                            · linarith only [h381, h384, h394, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h397 | h397
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h398 | h398
                                  · rcases h1bigk with h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h0, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h106, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h172, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h0, h221, h381, h383, h384, h396, h398, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p399_1]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      rcases p399_3 (m.d 0 1) (by simp) with h405 | h405
                                      · linarith only [h405, hlam, p399_0]
                                      · rcases p399_3 (m.d 1 2) (by simp) with h407 | h407
                                        · rcases p399_3 (m.d 1 3) (by simp) with h408 | h408
                                          · linarith only [h381, h408, hlam]
                                          · linarith only [h106, h408, hlam]
                                        · linarith only [h407, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h0, h221, h381, hc01, hc12, hlam, hphi, p399_1]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h172, h220, h383, h396, h398, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p399_1]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h0, h220, h221, h381, hlam, p399_2]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h220, h383, h384, h396, h398, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p399_1]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h381, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h384, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      rcases p399_3 (m.d 0 1) (by simp) with h420 | h420
                                      · linarith only [h106, h420, hlam]
                                      · linarith only [h220, h420, hlam]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      rcases p399_3 (m.d 0 1) (by simp) with h423 | h423
                                      · linarith only [h423, hlam, p399_0]
                                      · rcases p399_3 (m.d 1 2) (by simp) with h425 | h425
                                        · rcases p399_3 (m.d 1 3) (by simp) with h426 | h426
                                          · linarith only [h384, h426, hlam]
                                          · linarith only [h106, h426, hlam]
                                        · linarith only [h0, h425, hlam]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h382, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h106, h220, h383, h396, h398, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p399_1]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      rcases p399_3 (m.d 0 1) (by simp) with h433 | h433
                                      · linarith only [h172, h433, hlam]
                                      · linarith only [h220, h433, hlam]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h220, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h383, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h392, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [h393, hlam, p399_0]
                                    · have p399_0 := h399c.1
                                      have p399_1 := h399c.2.1
                                      have p399_2 := h399c.2.2.1
                                      have p399_3 := h399c.2.2.2
                                      linarith only [hlam, p399_0]
                                  · linarith only [h398, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h220, h221, h393, h394, h397, hlam]
                              · linarith only [h0, h221, h396, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h393, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h221, h381, h392, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h383, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h221, h381, h382, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                  · linarith only [h0, h220, h303, h381, h448, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
                                  · rcases h1bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h0, hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h106, hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h172, hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h450, h455, h457, hc45, hlam, hphi, ht0b, ht5b, p458_1, u0elo0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h448, h454, hc01, hc23, hlam, hphi, ht12, p458_1]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h381, hlam, p458_1]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h448, hlam, p458_1]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      rcases p458_3 (m.d 0 1) (by simp) with h468 | h468
                                      · linarith only [h0, h468, hlam]
                                      · linarith only [h220, h468, hlam]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      rcases p458_3 (m.d 0 1) (by simp) with h471 | h471
                                      · linarith only [h471, hlam, p458_0]
                                      · rcases p458_3 (m.d 1 2) (by simp) with h473 | h473
                                        · linarith only [h381, h473, hlam]
                                        · linarith only [h0, h473, hlam]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h0, h220, h381, h450, h455, h457, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h0, h220, h381, h448, h450, h455, h457, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h0, h220, h221, h341, h451, hlam, p458_2]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      rcases p458_3 (m.d 0 1) (by simp) with h480 | h480
                                      · linarith only [h480, hlam, p458_0]
                                      · rcases p458_3 (m.d 1 2) (by simp) with h482 | h482
                                        · linarith only [h448, h482, hlam]
                                        · linarith only [h0, h482, hlam]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, p458_1]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h451, hlam, p458_1]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      rcases p458_3 (m.d 0 1) (by simp) with h488 | h488
                                      · linarith only [h172, h488, hlam]
                                      · linarith only [h220, h488, hlam]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h220, hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h450, hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h452, hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [h453, hlam, p458_0]
                                    · have p458_0 := h458c.1
                                      have p458_1 := h458c.2.1
                                      have p458_2 := h458c.2.2.1
                                      have p458_3 := h458c.2.2.2
                                      linarith only [hlam, p458_0]
                                  · linarith only [h221, h341, h457, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                · linarith only [h0, h220, h448, h453, h456, hlam]
                              · linarith only [h0, h221, h341, h381, h451, h455, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h381, h451, h454, hlam]
                          · linarith only [h453, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h221, h341, h451, h452, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
                            · linarith only [h106, h220, h450, h451, h504, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h220, h381, h450, h504, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h220, h381, h450, h451, h503, hc25, hlam, hphi, u5elo4]
                        · linarith only [h0, h220, h381, h450, h502, hc25, hlam, hphi, u5elo3]
                    · linarith only [h0, h450, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h220, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT1_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5bigk := hb5.1
  have h1ehi := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h3 | h3
    · rcases p0_3 (m.d 1 5) (by simp) with h4 | h4
      · rcases p0_3 (m.d 2 5) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 0 1 4 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h12, h4, hlam]
                    · linarith only [h12, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h11, h9, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h10, h9, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h9, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h18 | h18
              · rcases m.htr 0 1 3 (by decide) (by decide) with h19 | h19
                · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h21 | h21
                    · linarith only [h21, h4, hlam]
                    · linarith only [h18, h21, hc15, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h18, h20, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h18, h19, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h18, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
              · rcases m.htr 0 1 3 (by decide) (by decide) with h29 | h29
                · rcases m.htr 0 1 4 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h31, h4, hlam]
                    · linarith only [h28, h31, hc15, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h28, h30, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h28, h29, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h28, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h37 | h37
              · rcases m.htr 0 1 3 (by decide) (by decide) with h38 | h38
                · rcases m.htr 0 1 4 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
                    · linarith only [h4, h40, hlam]
                    · linarith only [h40, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h37, h39, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h37, h38, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h37, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h4, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h3, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h48 | h48
    · rcases p0_3 (m.d 1 5) (by simp) with h49 | h49
      · rcases p0_3 (m.d 2 5) (by simp) with h50 | h50
        · rcases p0_3 (m.d 3 5) (by simp) with h51 | h51
          · linarith only [h51, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · rcases m.htr 0 1 3 (by decide) (by decide) with h55 | h55
                · rcases m.htr 0 1 4 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h57 | h57
                    · linarith only [h49, h57, hlam]
                    · linarith only [h54, h57, hc15, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h54, h56, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h54, h55, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h54, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h63 | h63
              · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
                · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h66 | h66
                    · linarith only [h49, h66, hlam]
                    · linarith only [h66, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h63, h65, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h63, h64, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h63, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 5) (by simp) with h72 | h72
          · linarith only [h72, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h74 | h74
            · rcases m.htr 0 1 2 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 1 3 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h49, h78, hlam]
                    · linarith only [h78, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h75, h77, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h75, h76, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h75, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
              · rcases m.htr 0 1 3 (by decide) (by decide) with h85 | h85
                · rcases m.htr 0 1 4 (by decide) (by decide) with h86 | h86
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h87 | h87
                    · linarith only [h49, h87, hlam]
                    · linarith only [h87, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h84, h86, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h84, h85, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h84, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h49, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h48, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h95 | h95
    · rcases p0_3 (m.d 1 5) (by simp) with h96 | h96
      · rcases p0_3 (m.d 2 5) (by simp) with h97 | h97
        · rcases p0_3 (m.d 3 5) (by simp) with h98 | h98
          · rcases p0_3 (m.d 4 5) (by simp) with h99 | h99
            · linarith only [h99, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h101 | h101
              · rcases m.htr 0 1 3 (by decide) (by decide) with h102 | h102
                · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
                    · linarith only [h104, h96, hlam]
                    · linarith only [h101, h104, hc15, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h101, h103, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h101, h102, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h101, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h110 | h110
            · linarith only [h110, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h115, h96, hlam]
                    · linarith only [h115, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h112, h114, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h112, h113, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h112, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 5) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h124 | h124
              · rcases m.htr 0 1 3 (by decide) (by decide) with h125 | h125
                · rcases m.htr 0 1 4 (by decide) (by decide) with h126 | h126
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h127 | h127
                    · linarith only [h127, h96, hlam]
                    · linarith only [h124, h127, hc15, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h124, h126, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h124, h125, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h124, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h133 | h133
            · linarith only [h133, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
              · rcases m.htr 0 1 3 (by decide) (by decide) with h136 | h136
                · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h138 | h138
                    · linarith only [h138, h96, hlam]
                    · linarith only [h138, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h135, h137, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h135, h136, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h135, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h96, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h95, hlam, p0_0]
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
    rcases p0_3 (m.d 0 5) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 5) (by simp) with h149 | h149
      · rcases p0_3 (m.d 2 5) (by simp) with h150 | h150
        · linarith only [h150, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · rcases m.htr 0 1 2 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 1 3 (by decide) (by decide) with h155 | h155
                · rcases m.htr 0 1 4 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h157 | h157
                    · linarith only [h157, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h148, h157, hlam]
                  · linarith only [h156, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h154, h155, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h154, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 1 3 (by decide) (by decide) with h164 | h164
                · rcases m.htr 0 1 4 (by decide) (by decide) with h165 | h165
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h166 | h166
                    · linarith only [h166, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h148, h166, hlam]
                  · linarith only [h165, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h163, h164, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h163, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h172 | h172
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · rcases m.htr 0 1 3 (by decide) (by decide) with h174 | h174
                · rcases m.htr 0 1 4 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
                    · linarith only [h176, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h148, h176, hlam]
                  · linarith only [h175, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h173, h174, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h173, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h182 | h182
              · rcases m.htr 0 1 3 (by decide) (by decide) with h183 | h183
                · rcases m.htr 0 1 4 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h185 | h185
                    · linarith only [h185, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h148, h185, hlam]
                  · linarith only [h184, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h182, h183, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h182, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h149, hlam, p0_0]
    · linarith only [h148, hc15, hlam, hphi, ht01, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h193 | h193
    · rcases p0_3 (m.d 1 5) (by simp) with h194 | h194
      · rcases p0_3 (m.d 2 5) (by simp) with h195 | h195
        · rcases p0_3 (m.d 3 5) (by simp) with h196 | h196
          · linarith only [h196, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 3 (by decide) (by decide) with h200 | h200
                · rcases m.htr 0 1 4 (by decide) (by decide) with h201 | h201
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h202 | h202
                    · linarith only [h202, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h193, h202, hlam]
                  · linarith only [h201, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h199, h200, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h199, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h208 | h208
              · rcases m.htr 0 1 3 (by decide) (by decide) with h209 | h209
                · rcases m.htr 0 1 4 (by decide) (by decide) with h210 | h210
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h211 | h211
                    · linarith only [h211, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h193, h211, hlam]
                  · linarith only [h210, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h208, h209, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h208, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 5) (by simp) with h217 | h217
          · linarith only [h217, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h219 | h219
            · rcases m.htr 0 1 2 (by decide) (by decide) with h220 | h220
              · rcases m.htr 0 1 3 (by decide) (by decide) with h221 | h221
                · rcases m.htr 0 1 4 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h223 | h223
                    · linarith only [h223, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h193, h223, hlam]
                  · linarith only [h222, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h220, h221, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h220, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h229 | h229
              · rcases m.htr 0 1 3 (by decide) (by decide) with h230 | h230
                · rcases m.htr 0 1 4 (by decide) (by decide) with h231 | h231
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h232 | h232
                    · linarith only [h232, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h193, h232, hlam]
                  · linarith only [h231, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h229, h230, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h229, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h194, hlam, p0_0]
    · linarith only [h193, hc15, hlam, hphi, ht01, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h240 | h240
    · rcases p0_3 (m.d 1 5) (by simp) with h241 | h241
      · rcases p0_3 (m.d 2 5) (by simp) with h242 | h242
        · rcases p0_3 (m.d 3 5) (by simp) with h243 | h243
          · rcases p0_3 (m.d 4 5) (by simp) with h244 | h244
            · linarith only [h244, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h246 | h246
              · rcases m.htr 0 1 3 (by decide) (by decide) with h247 | h247
                · rcases m.htr 0 1 4 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h249 | h249
                    · linarith only [h249, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h240, h249, hlam]
                  · linarith only [h248, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h246, h247, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h246, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h255 | h255
            · linarith only [h255, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h257 | h257
              · rcases m.htr 0 1 3 (by decide) (by decide) with h258 | h258
                · rcases m.htr 0 1 4 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h260 | h260
                    · linarith only [h260, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h240, h260, hlam]
                  · linarith only [h259, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h257, h258, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h257, hc12, hlam, hphi, ht01, u0ehi0]
        · rcases p0_3 (m.d 3 5) (by simp) with h266 | h266
          · rcases p0_3 (m.d 4 5) (by simp) with h267 | h267
            · linarith only [h267, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h269 | h269
              · rcases m.htr 0 1 3 (by decide) (by decide) with h270 | h270
                · rcases m.htr 0 1 4 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h272 | h272
                    · linarith only [h272, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h240, h272, hlam]
                  · linarith only [h271, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h269, h270, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h269, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h278 | h278
            · linarith only [h278, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
              · rcases m.htr 0 1 3 (by decide) (by decide) with h281 | h281
                · rcases m.htr 0 1 4 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h283 | h283
                    · linarith only [h283, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h240, h283, hlam]
                  · linarith only [h282, hc14, hlam, hphi, ht01, u0ehi0]
                · linarith only [h280, h281, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h280, hc12, hlam, hphi, ht01, u0ehi0]
      · linarith only [h241, hlam, p0_0]
    · linarith only [h240, hc15, hlam, hphi, ht01, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht12, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h294 | h294
    · rcases p0_3 (m.d 1 5) (by simp) with h295 | h295
      · rcases p0_3 (m.d 2 5) (by simp) with h296 | h296
        · rcases p0_3 (m.d 3 5) (by simp) with h297 | h297
          · linarith only [h297, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h299 | h299
            · rcases m.htr 0 1 2 (by decide) (by decide) with h300 | h300
              · rcases m.htr 0 1 3 (by decide) (by decide) with h301 | h301
                · rcases m.htr 0 1 4 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h303 | h303
                    · linarith only [h295, h303, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h303, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h300, h302, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h300, h301, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h300, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
                · rcases m.htr 0 1 4 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
                    · linarith only [h295, h312, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h312, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h309, h311, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h309, h310, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h309, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h296, hlam, p0_0]
      · linarith only [h294, h295, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h294, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h321 | h321
    · rcases p0_3 (m.d 1 5) (by simp) with h322 | h322
      · rcases p0_3 (m.d 2 5) (by simp) with h323 | h323
        · rcases p0_3 (m.d 3 5) (by simp) with h324 | h324
          · rcases p0_3 (m.d 4 5) (by simp) with h325 | h325
            · linarith only [h325, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h327 | h327
              · rcases m.htr 0 1 3 (by decide) (by decide) with h328 | h328
                · rcases m.htr 0 1 4 (by decide) (by decide) with h329 | h329
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h330 | h330
                    · linarith only [h322, h330, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h330, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h327, h329, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h327, h328, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h327, hc12, hlam, hphi, ht01, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h336 | h336
            · linarith only [h336, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h338 | h338
              · rcases m.htr 0 1 3 (by decide) (by decide) with h339 | h339
                · rcases m.htr 0 1 4 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h341 | h341
                    · linarith only [h322, h341, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h341, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h338, h340, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h338, h339, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h338, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h323, hlam, p0_0]
      · linarith only [h321, h322, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h321, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht12, ht23, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h352 | h352
    · rcases p0_3 (m.d 1 5) (by simp) with h353 | h353
      · rcases p0_3 (m.d 2 5) (by simp) with h354 | h354
        · linarith only [h354, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h356 | h356
          · rcases p0_3 (m.d 4 5) (by simp) with h357 | h357
            · rcases m.htr 0 1 2 (by decide) (by decide) with h358 | h358
              · rcases m.htr 0 1 3 (by decide) (by decide) with h359 | h359
                · rcases m.htr 0 1 4 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h361 | h361
                    · linarith only [h353, h361, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h361, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h358, h360, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h358, h359, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h358, hc12, hlam, hphi, ht01, u0ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h367 | h367
              · rcases m.htr 0 1 3 (by decide) (by decide) with h368 | h368
                · rcases m.htr 0 1 4 (by decide) (by decide) with h369 | h369
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h370 | h370
                    · linarith only [h353, h370, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h370, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h367, h369, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h367, h368, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h367, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h356, hlam, p0_0]
      · linarith only [h352, h353, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h352, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h380 | h380
    · rcases p0_3 (m.d 1 5) (by simp) with h381 | h381
      · rcases p0_3 (m.d 2 5) (by simp) with h382 | h382
        · rcases p0_3 (m.d 3 5) (by simp) with h383 | h383
          · rcases p0_3 (m.d 4 5) (by simp) with h384 | h384
            · linarith only [h384, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h386 | h386
              · rcases m.htr 0 1 3 (by decide) (by decide) with h387 | h387
                · rcases m.htr 0 1 4 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h389 | h389
                    · linarith only [h381, h389, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h389, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h386, h388, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h386, h387, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h386, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h383, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h396 | h396
          · rcases p0_3 (m.d 4 5) (by simp) with h397 | h397
            · linarith only [h397, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h399 | h399
              · rcases m.htr 0 1 3 (by decide) (by decide) with h400 | h400
                · rcases m.htr 0 1 4 (by decide) (by decide) with h401 | h401
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h402 | h402
                    · linarith only [h381, h402, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h402, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h399, h401, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h399, h400, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h399, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h396, hlam, p0_0]
      · linarith only [h380, h381, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h380, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
    · rcases p0_3 (m.d 1 5) (by simp) with h414 | h414
      · rcases p0_3 (m.d 2 5) (by simp) with h415 | h415
        · linarith only [h415, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h417 | h417
          · rcases p0_3 (m.d 4 5) (by simp) with h418 | h418
            · rcases m.htr 0 1 2 (by decide) (by decide) with h419 | h419
              · rcases m.htr 0 1 3 (by decide) (by decide) with h420 | h420
                · rcases m.htr 0 1 4 (by decide) (by decide) with h421 | h421
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h422 | h422
                    · linarith only [h414, h422, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h422, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h419, h421, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h419, h420, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h419, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h418, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h429 | h429
            · rcases m.htr 0 1 2 (by decide) (by decide) with h430 | h430
              · rcases m.htr 0 1 3 (by decide) (by decide) with h431 | h431
                · rcases m.htr 0 1 4 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h433 | h433
                    · linarith only [h414, h433, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h433, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h430, h432, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h430, h431, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h430, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h429, hlam, p0_0]
      · linarith only [h413, h414, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h413, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h442 | h442
    · rcases p0_3 (m.d 1 5) (by simp) with h443 | h443
      · rcases p0_3 (m.d 2 5) (by simp) with h444 | h444
        · rcases p0_3 (m.d 3 5) (by simp) with h445 | h445
          · linarith only [h445, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h447 | h447
            · rcases m.htr 0 1 2 (by decide) (by decide) with h448 | h448
              · rcases m.htr 0 1 3 (by decide) (by decide) with h449 | h449
                · rcases m.htr 0 1 4 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h451 | h451
                    · linarith only [h443, h451, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h451, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h448, h450, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h448, h449, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h448, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h447, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h458 | h458
          · linarith only [h458, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h460 | h460
            · rcases m.htr 0 1 2 (by decide) (by decide) with h461 | h461
              · rcases m.htr 0 1 3 (by decide) (by decide) with h462 | h462
                · rcases m.htr 0 1 4 (by decide) (by decide) with h463 | h463
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h464 | h464
                    · linarith only [h443, h464, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                    · linarith only [h464, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h461, h463, hc14, hlam, hphi, ht01, u0ehi1]
                · linarith only [h461, h462, hc13, hlam, hphi, ht01, u0ehi1]
              · linarith only [h461, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h460, hlam, p0_0]
      · linarith only [h442, h443, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi4]
    · linarith only [h442, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_M_IR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1bigk := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
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
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h5, hlam]
                · linarith only [h10, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h9, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h14 | h14
            · linarith only [h14, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · linarith only [h17, h5, hlam]
                · linarith only [h14, h17, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h16, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 1 5) (by simp) with h22 | h22
            · linarith only [h22, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h21, h26, hlam]
                  · linarith only [h22, h26, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h25, h5, hlam, p0_1]
              · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h31 | h31
            · linarith only [h31, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                                  · linarith only [h43, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · linarith only [h31, h43, hlam]
                                · linarith only [h21, h42, hlam]
                              · linarith only [h41, h5, hlam]
                            · linarith only [h40, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h39, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                                · linarith only [h37, h38, h53, hc01, hlam, hphi, p0_1, u0ehi2]
                                · linarith only [h21, h53, hlam]
                              · linarith only [h5, h52, hlam]
                            · linarith only [h38, h50, h51, hlam, hphi, u5ehi7, u5elo4]
                          · linarith only [h37, h50, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo2]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
                              · linarith only [h37, h59, h61, h62, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
                              · linarith only [h5, h62, hlam]
                            · linarith only [h61, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h59, h60, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h67 | h67
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                              · linarith only [h37, h67, h69, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                              · linarith only [h5, h69, hlam]
                            · linarith only [h59, h67, h68, hlam, hphi, u5ehi7, u5elo4]
                          · linarith only [h67, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                    · linarith only [h36, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
                  · linarith only [h31, h35, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h31, h34, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h33, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h79 | h79
    · rcases p0_3 (m.d 1 2) (by simp) with h80 | h80
      · rcases p0_3 (m.d 1 3) (by simp) with h81 | h81
        · linarith only [h81, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 1 5) (by simp) with h84 | h84
            · linarith only [h84, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h86 | h86
              · linarith only [h80, h86, hlam]
              · linarith only [h84, h86, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h89 | h89
            · linarith only [h89, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h91 | h91
              · linarith only [h80, h91, hlam]
              · linarith only [h89, h91, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h94 | h94
        · linarith only [h94, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h96 | h96
          · rcases p0_3 (m.d 1 5) (by simp) with h97 | h97
            · linarith only [h80, h97, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h99 | h99
              · rcases m.htr 0 1 3 (by decide) (by decide) with h100 | h100
                · rcases m.htr 0 1 4 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h96, hlam]
                  · linarith only [h101, h97, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h100, hlam, p0_0]
              · linarith only [h97, h99, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h106 | h106
            · linarith only [h106, h80, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 1 3 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 1 4 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h112 | h112
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h113 | h113
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h114 | h114
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h115 | h115
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                              · linarith only [h116, h80, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
                                  · linarith only [h116, h119, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · linarith only [h114, h118, h119, hc24, hlam, hphi, ht45, u5elo0]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                                  · linarith only [h116, h122, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                                      · linarith only [h125, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi8]
                                      · linarith only [h106, h125, hlam]
                                    · linarith only [h124, h96, hlam]
                            · linarith only [h115, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h112, h114, hc23, hlam, hphi, ht34, ht45, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                              · linarith only [h133, h80, hlam]
                              · linarith only [h112, h113, h133, hc12, hc24, hlam, hphi]
                            · linarith only [h112, h113, h132, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h112, h131, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo2]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h138 | h138
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h140 | h140
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
                              · linarith only [h141, h80, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                                  · linarith only [h141, h144, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · linarith only [h112, h139, h144, hc12, hc23, hlam, hphi]
                                · linarith only [h112, h138, h143, hc12, hc23, hlam, hphi]
                            · linarith only [h140, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h138, h139, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h150 | h150
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h151 | h151
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
                              · linarith only [h152, h80, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
                                · linarith only [h138, h150, h154, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                                  · linarith only [h152, h156, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · linarith only [h138, h150, h156, hc12, hc24, hlam, hphi]
                            · linarith only [h138, h150, h151, hlam, hphi, u5ehi7, u5elo4]
                          · linarith only [h150, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                    · linarith only [h111, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
                  · linarith only [h110, h96, hlam, p0_1]
                · linarith only [h109, hlam, p0_0]
              · linarith only [h106, h108, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
    · linarith only [h79, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h166 | h166
    · rcases p0_3 (m.d 1 2) (by simp) with h167 | h167
      · rcases p0_3 (m.d 1 3) (by simp) with h168 | h168
        · rcases p0_3 (m.d 1 4) (by simp) with h169 | h169
          · linarith only [h169, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h171 | h171
            · linarith only [h171, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
              · linarith only [h167, h173, hlam]
              · linarith only [h171, h173, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h176 | h176
          · linarith only [h176, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h178 | h178
            · linarith only [h168, h178, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h180 | h180
              · linarith only [h167, h180, hlam]
              · linarith only [h178, h180, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h183 | h183
        · rcases p0_3 (m.d 1 4) (by simp) with h184 | h184
          · linarith only [h184, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h186 | h186
            · linarith only [h167, h186, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h188 | h188
              · rcases m.htr 0 1 3 (by decide) (by decide) with h189 | h189
                · linarith only [h183, h189, hlam]
                · linarith only [h186, h189, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h186, h188, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h193 | h193
          · linarith only [h193, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h195 | h195
            · linarith only [h167, h195, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 1 3 (by decide) (by decide) with h198 | h198
                · rcases m.htr 0 1 4 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h201 | h201
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h202 | h202
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h203 | h203
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h204 | h204
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
                                · linarith only [h167, h206, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
                                  · linarith only [h206, h208, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · linarith only [h203, h205, h208, hc23, hlam, hphi, ht34, ht45, u5elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                                · linarith only [h167, h211, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                                  · linarith only [h211, h213, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                                    · linarith only [h183, h215, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
                                      · linarith only [h215, h217, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi8]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                                        · linarith only [h219, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
                                        · linarith only [h195, h219, hlam]
                            · linarith only [h204, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h203, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h224 | h224
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
                                · linarith only [h167, h227, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
                                  · linarith only [h227, h229, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · linarith only [h202, h224, h229, hc12, hc24, hlam, hphi]
                              · linarith only [h201, h202, h226, hc12, hc24, hlam, hphi]
                            · linarith only [h201, h202, h225, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h201, h224, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo2]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h235 | h235
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h236 | h236
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
                              · linarith only [h201, h235, h237, h238, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                                · linarith only [h167, h240, hlam]
                                · linarith only [h201, h235, h240, hc12, hc23, hlam, hphi]
                            · linarith only [h237, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h235, h236, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h246 | h246
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
                              · linarith only [h201, h245, h247, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
                                · linarith only [h167, h249, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                                  · linarith only [h249, h251, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                                  · linarith only [h201, h245, h251, hc12, hc23, hlam, hphi]
                            · linarith only [h235, h245, h246, hlam, hphi, u5ehi7, u5elo4]
                          · linarith only [h245, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                    · linarith only [h183, h200, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
                  · linarith only [h199, hlam, p0_0]
                · linarith only [h195, h198, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h195, h197, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
    · linarith only [h166, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h261 | h261
    · rcases p0_3 (m.d 1 2) (by simp) with h262 | h262
      · rcases p0_3 (m.d 1 3) (by simp) with h263 | h263
        · rcases p0_3 (m.d 1 4) (by simp) with h264 | h264
          · rcases p0_3 (m.d 1 5) (by simp) with h265 | h265
            · linarith only [h265, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h267 | h267
              · linarith only [h262, h267, hlam]
              · linarith only [h267, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h270 | h270
            · linarith only [h270, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · linarith only [h262, h272, hlam]
              · linarith only [h272, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h275 | h275
          · rcases p0_3 (m.d 1 5) (by simp) with h276 | h276
            · linarith only [h276, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h278 | h278
              · linarith only [h262, h278, hlam]
              · linarith only [h278, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h281 | h281
            · linarith only [h281, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h283 | h283
              · linarith only [h262, h283, hlam]
              · linarith only [h283, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h286 | h286
        · rcases p0_3 (m.d 1 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 1 5) (by simp) with h288 | h288
            · linarith only [h288, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
              · rcases m.htr 0 1 3 (by decide) (by decide) with h291 | h291
                · linarith only [h286, h291, hlam]
                · linarith only [h291, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h262, h290, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h295 | h295
            · linarith only [h295, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h297 | h297
              · rcases m.htr 0 1 3 (by decide) (by decide) with h298 | h298
                · linarith only [h286, h298, hlam]
                · linarith only [h298, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h262, h297, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h302 | h302
          · rcases p0_3 (m.d 1 5) (by simp) with h303 | h303
            · linarith only [h303, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h305 | h305
              · rcases m.htr 0 1 3 (by decide) (by decide) with h306 | h306
                · rcases m.htr 0 1 4 (by decide) (by decide) with h307 | h307
                  · linarith only [h302, h307, hlam]
                  · linarith only [h307, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h286, h306, hlam, p0_1]
              · linarith only [h262, h305, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h312 | h312
            · linarith only [h312, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h314 | h314
              · rcases m.htr 0 1 3 (by decide) (by decide) with h315 | h315
                · rcases m.htr 0 1 4 (by decide) (by decide) with h316 | h316
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h317 | h317
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h318 | h318
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h319 | h319
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h320 | h320
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                                  · linarith only [h262, h324, hlam]
                                  · linarith only [h322, h324, hc23, hlam, hphi, ht34, ht45, u5elo2]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
                                  · linarith only [h262, h327, hlam]
                                  · linarith only [h320, h322, h327, hc23, hlam, hphi, ht34, ht45, u5elo0]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                                  · linarith only [h262, h331, hlam]
                                  · linarith only [h320, h330, h331, hc24, hlam, hphi, ht45, u5elo0]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                                  · linarith only [h262, h334, hlam]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                                      · linarith only [h286, h337, hlam]
                                      · linarith only [h336, h337, hc34, hlam, hphi, ht45, u5elo3]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
                                      · linarith only [h286, h340, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h342 | h342
                                        · linarith only [h302, h342, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h345 | h345
                                            · rcases m.htr 3 4 5 (by decide) (by decide) with h346 | h346
                                              · linarith only [h314, h318, h322, h336, h342, h344, h346, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                              · linarith only [h322, h336, h346, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                            · linarith only [h322, h345, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                                            · linarith only [h322, h340, h344, h350, hc12, hc34, hlam, hphi, ht23]
                                            · linarith only [h322, h350, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h321, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h320, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h355 | h355
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h356 | h356
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h357 | h357
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                                · linarith only [h318, h319, h358, hc12, hlam, hphi, ht01, u0ehi2]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                                  · linarith only [h262, h360, hlam]
                                  · linarith only [h319, h355, h360, hc12, hc24, hlam, hphi]
                              · linarith only [h318, h319, h357, hc12, hc24, hlam, hphi]
                            · linarith only [h318, h319, h356, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h318, h355, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo2]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h367 | h367
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h369 | h369
                              · linarith only [h318, h366, h368, h369, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                                  · linarith only [h262, h372, hlam]
                                  · linarith only [h371, h372, hc24, hlam, hphi, ht45, u5elo2]
                                · linarith only [h318, h366, h371, hc12, hc23, hlam, hphi]
                            · linarith only [h368, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                          · linarith only [h366, h367, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h378 | h378
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h379 | h379
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
                              · linarith only [h262, h318, h378, h380, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi7]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                                · linarith only [h286, h366, h378, h380, h382, hc01, hlam, hphi, p0_1, u0ehi4, u5ehi7, u5elo0]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h384 | h384
                                  · linarith only [h262, h384, hlam]
                                  · linarith only [h318, h378, h384, hc12, hc23, hlam, hphi]
                            · linarith only [h366, h378, h379, hlam, hphi, u5ehi7, u5elo4]
                          · linarith only [h378, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
                    · linarith only [h317, hlam, p0_0]
                  · linarith only [h316, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h286, h315, hlam, p0_1]
              · linarith only [h314, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
    · linarith only [h261, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h396 | h396
    · rcases p0_3 (m.d 1 2) (by simp) with h397 | h397
      · rcases p0_3 (m.d 1 3) (by simp) with h398 | h398
        · linarith only [h398, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h400 | h400
          · rcases p0_3 (m.d 1 5) (by simp) with h401 | h401
            · linarith only [h401, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h403 | h403
              · linarith only [h401, h403, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h396, h403, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h406 | h406
            · linarith only [h406, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h408 | h408
              · linarith only [h406, h408, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h396, h408, hlam]
      · linarith only [h397, hlam, p0_0]
    · linarith only [h396, hc12, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h413 | h413
    · rcases p0_3 (m.d 1 2) (by simp) with h414 | h414
      · rcases p0_3 (m.d 1 3) (by simp) with h415 | h415
        · rcases p0_3 (m.d 1 4) (by simp) with h416 | h416
          · linarith only [h416, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h418 | h418
            · linarith only [h418, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h420 | h420
              · linarith only [h418, h420, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h413, h420, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h423 | h423
          · linarith only [h423, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h425 | h425
            · linarith only [h415, h425, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h427 | h427
              · linarith only [h425, h427, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h413, h427, hlam]
      · linarith only [h414, hlam, p0_0]
    · linarith only [h413, hc12, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h432 | h432
    · rcases p0_3 (m.d 1 2) (by simp) with h433 | h433
      · rcases p0_3 (m.d 1 3) (by simp) with h434 | h434
        · rcases p0_3 (m.d 1 4) (by simp) with h435 | h435
          · rcases p0_3 (m.d 1 5) (by simp) with h436 | h436
            · linarith only [h436, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h438 | h438
              · linarith only [h438, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h432, h438, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h441 | h441
            · linarith only [h441, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h443 | h443
              · linarith only [h443, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h432, h443, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h446 | h446
          · rcases p0_3 (m.d 1 5) (by simp) with h447 | h447
            · linarith only [h447, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h449 | h449
              · linarith only [h449, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h432, h449, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h452 | h452
            · linarith only [h452, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h454 | h454
              · linarith only [h454, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h432, h454, hlam]
      · linarith only [h433, hlam, p0_0]
    · linarith only [h432, hc12, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h460 | h460
    · rcases p0_3 (m.d 1 2) (by simp) with h461 | h461
      · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h463 | h463
        · rcases p0_3 (m.d 1 4) (by simp) with h464 | h464
          · rcases p0_3 (m.d 1 5) (by simp) with h465 | h465
            · linarith only [h465, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h467 | h467
              · rcases m.htr 0 1 3 (by decide) (by decide) with h468 | h468
                · linarith only [h465, h468, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h460, h468, hlam]
              · linarith only [h467, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h472 | h472
            · linarith only [h472, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h474 | h474
              · rcases m.htr 0 1 3 (by decide) (by decide) with h475 | h475
                · linarith only [h472, h475, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h460, h475, hlam]
              · linarith only [h474, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h463, hlam, p0_0]
    · linarith only [h460, hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h482 | h482
    · rcases p0_3 (m.d 1 2) (by simp) with h483 | h483
      · rcases p0_3 (m.d 1 3) (by simp) with h484 | h484
        · rcases p0_3 (m.d 1 4) (by simp) with h485 | h485
          · linarith only [h485, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
            · linarith only [h487, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
              · linarith only [h483, h487, h489, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h482, h487, h489, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · linarith only [h484, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h493 | h493
        · rcases p0_3 (m.d 1 4) (by simp) with h494 | h494
          · linarith only [h494, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h496 | h496
            · linarith only [h483, h496, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h498 | h498
              · rcases m.htr 0 1 3 (by decide) (by decide) with h499 | h499
                · linarith only [h496, h499, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h482, h499, hlam]
              · linarith only [h482, h496, h498, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · linarith only [h493, hlam, p0_0]
    · linarith only [h482, hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h505 | h505
    · rcases p0_3 (m.d 1 2) (by simp) with h506 | h506
      · rcases p0_3 (m.d 1 3) (by simp) with h507 | h507
        · rcases p0_3 (m.d 1 4) (by simp) with h508 | h508
          · rcases p0_3 (m.d 1 5) (by simp) with h509 | h509
            · linarith only [h509, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h511 | h511
              · linarith only [h506, h511, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h505, h511, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h514 | h514
            · linarith only [h514, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h516 | h516
              · linarith only [h506, h516, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h505, h516, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
        · linarith only [h507, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h520 | h520
        · rcases p0_3 (m.d 1 4) (by simp) with h521 | h521
          · rcases p0_3 (m.d 1 5) (by simp) with h522 | h522
            · linarith only [h522, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h524 | h524
              · rcases m.htr 0 1 3 (by decide) (by decide) with h525 | h525
                · linarith only [h525, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h505, h525, hlam]
              · linarith only [h506, h524, hc01, hc13, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h529 | h529
            · linarith only [h529, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h531 | h531
              · rcases m.htr 0 1 3 (by decide) (by decide) with h532 | h532
                · linarith only [h532, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h505, h532, hlam]
              · linarith only [h506, h531, hc01, hc13, hlam, hphi, p0_1]
        · linarith only [h520, hlam, p0_0]
    · linarith only [h505, hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h539 | h539
    · rcases p0_3 (m.d 1 2) (by simp) with h540 | h540
      · linarith only [h540, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h542 | h542
        · rcases p0_3 (m.d 1 4) (by simp) with h543 | h543
          · rcases p0_3 (m.d 1 5) (by simp) with h544 | h544
            · linarith only [h544, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h546 | h546
              · rcases m.htr 0 1 3 (by decide) (by decide) with h547 | h547
                · linarith only [h542, h544, h547, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h539, h544, h547, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h539, h546, hlam, p0_1]
          · linarith only [h543, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h552 | h552
          · rcases p0_3 (m.d 1 5) (by simp) with h553 | h553
            · linarith only [h553, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h555 | h555
              · rcases m.htr 0 1 3 (by decide) (by decide) with h556 | h556
                · rcases m.htr 0 1 4 (by decide) (by decide) with h557 | h557
                  · linarith only [h553, h557, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                  · linarith only [h539, h557, hlam]
                · linarith only [h542, h556, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h539, h555, hlam, p0_1]
          · linarith only [h552, hlam, p0_0]
    · linarith only [h539, hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h564 | h564
    · rcases p0_3 (m.d 1 2) (by simp) with h565 | h565
      · rcases p0_3 (m.d 1 3) (by simp) with h566 | h566
        · linarith only [h566, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h568 | h568
          · rcases p0_3 (m.d 1 5) (by simp) with h569 | h569
            · linarith only [h569, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h571 | h571
              · linarith only [h565, h569, h571, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h564, h569, h571, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · linarith only [h568, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h575 | h575
        · linarith only [h575, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h577 | h577
          · rcases p0_3 (m.d 1 5) (by simp) with h578 | h578
            · linarith only [h565, h578, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h580 | h580
              · rcases m.htr 0 1 3 (by decide) (by decide) with h581 | h581
                · rcases m.htr 0 1 4 (by decide) (by decide) with h582 | h582
                  · linarith only [h578, h582, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                  · linarith only [h564, h582, hlam]
                · linarith only [h581, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h564, h565, h580, hlam, p0_1]
          · linarith only [h577, hlam, p0_0]
    · linarith only [h564, hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h590 | h590
    · rcases p0_3 (m.d 1 2) (by simp) with h591 | h591
      · rcases p0_3 (m.d 1 3) (by simp) with h592 | h592
        · rcases p0_3 (m.d 1 4) (by simp) with h593 | h593
          · rcases p0_3 (m.d 1 5) (by simp) with h594 | h594
            · linarith only [h594, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h596 | h596
              · linarith only [h591, h596, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h590, h596, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · linarith only [h593, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h600 | h600
          · rcases p0_3 (m.d 1 5) (by simp) with h601 | h601
            · linarith only [h601, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h603 | h603
              · linarith only [h591, h603, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h590, h603, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
          · linarith only [h600, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h607 | h607
        · rcases p0_3 (m.d 1 4) (by simp) with h608 | h608
          · rcases p0_3 (m.d 1 5) (by simp) with h609 | h609
            · linarith only [h609, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h611 | h611
              · rcases m.htr 0 1 3 (by decide) (by decide) with h612 | h612
                · linarith only [h607, h612, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                · linarith only [h590, h612, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi6]
              · linarith only [h590, h591, h611, hlam, p0_1]
          · linarith only [h608, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h617 | h617
          · rcases p0_3 (m.d 1 5) (by simp) with h618 | h618
            · linarith only [h618, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h620 | h620
              · rcases m.htr 0 1 3 (by decide) (by decide) with h621 | h621
                · rcases m.htr 0 1 4 (by decide) (by decide) with h622 | h622
                  · linarith only [h622, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi6]
                  · linarith only [h590, h622, hlam]
                · linarith only [h607, h621, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h590, h591, h620, hlam, p0_1]
          · linarith only [h617, hlam, p0_0]
    · linarith only [h590, hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_M_LI_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1elo := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
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
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h10, h15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h0, h10, h12, h15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h14, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h13, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h0, h12, h20, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h20, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h11, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h0, h10, h24, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h24, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                          · linarith only [h29, h33, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                                · linarith only [h0, h1, h31, h35, h37, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                                  · linarith only [h0, h31, h39, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h1, h35, h39, h7, hc23, hc34, hlam, hphi]
                              · linarith only [h30, h33, h36, hc13, hlam, hphi, ht34, ht45, u5elo0]
                            · linarith only [h31, h35, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h32, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                        · linarith only [h31, h4, h45, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h45, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h30, h7, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1, h29, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h51 | h51
              · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
                · linarith only [h4, h5, h52, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                          · linarith only [h52, h54, h58, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                                · linarith only [h0, h1, h52, h56, h60, h62, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                                  · linarith only [h0, h56, h64, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h64, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h61, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h60, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h57, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h4, h5, h56, hc12, hc24, hlam, hphi]
                    · linarith only [h55, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h54, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h4, h51, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 2 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                      · linarith only [h4, h74, h79, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                                    · linarith only [h1, h82, h87, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h87, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h2, h4, h74, h84, h86, hc45, hlam, hphi, u5elo3]
                                · linarith only [h2, h4, h74, h82, h84, h85, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                              · linarith only [h84, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h77, h83, hc13, hlam, hphi, ht34, ht45, u5elo0]
                          · linarith only [h76, h79, h81, h82, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h81, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h78, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h77, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h4, h74, h76, hlam]
              · linarith only [h75, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
                · rcases m.htr 0 3 5 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                      · linarith only [h0, h104, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                                    · linarith only [h1, h107, h112, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h112, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h110, h111, h74, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h0, h101, h106, h110, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h109, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h108, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h1, h101, h104, h106, h107, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h106, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h100, h103, h74, hc25, hlam, hphi, u5elo4]
                  · linarith only [h102, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
                      · linarith only [h100, h125, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                          · linarith only [h0, h101, h127, h128, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                                    · rcases h0bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h0, h127, h133, h134, hc45, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h0, h127, h133, h134, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h0, h101, h127, h133, h134, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        rcases p135_3 (m.d 0 1) (by simp) with h140 | h140
                                        · rcases p135_3 (m.d 0 2) (by simp) with h141 | h141
                                          · linarith only [h0, h141, hlam]
                                          · linarith only [h100, h141, hlam]
                                        · linarith only [h140, h3, hlam]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h0, hlam, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h4, hlam, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h74, hlam, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h101, h132, h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h1, hlam, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h101, h132, hc02, hc23, hlam, hphi, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h101, hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h100, h101, h132, h133, h134, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h2, hlam, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h0, h127, h133, h134, hc45, hlam, hphi, ht0b, ht5b, p135_1, u0elo3]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h0, h101, h127, h132, h133, h134, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        rcases p135_3 (m.d 0 1) (by simp) with h159 | h159
                                        · rcases p135_3 (m.d 0 2) (by simp) with h160 | h160
                                          · linarith only [h160, h74, hlam]
                                          · linarith only [h100, h160, hlam]
                                        · linarith only [h159, h3, hlam]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h3, hlam, p135_1]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h100, hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h123, hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [h124, hlam, p135_0]
                                      · have p135_0 := h135c.1
                                        have p135_1 := h135c.2.1
                                        have p135_2 := h135c.2.2.1
                                        have p135_3 := h135c.2.2.2
                                        linarith only [hlam, p135_0]
                                    · linarith only [h101, h134, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h101, h132, h133, h4, hc02, hc35, hlam, hphi, ht23]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h171 | h171
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h172 | h172
                                    · rcases h0bigk with h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h0, h127, hc25, hlam, hphi, ht01, ht0b, ht5b, p173_1, u1elo0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h0, h127, h171, h172, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p173_1, u1elo0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h0, h127, h171, h172, h74, hc45, hlam, hphi, ht01, ht0b, ht5b, p173_1, u1elo0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        rcases p173_3 (m.d 0 1) (by simp) with h178 | h178
                                        · rcases p173_3 (m.d 0 2) (by simp) with h179 | h179
                                          · linarith only [h0, h179, hlam]
                                          · linarith only [h100, h179, hlam]
                                        · linarith only [h178, h3, hlam]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h0, hlam, p173_1]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h4, hlam, p173_1]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h74, hlam, p173_1]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h132, h3, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p173_1]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h1, hlam, p173_1]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h0, h101, h127, h171, h172, hc45, hlam, hphi, ht0b, ht5b, p173_1, u0elo3]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h101, hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        rcases p173_3 (m.d 0 1) (by simp) with h192 | h192
                                        · rcases p173_3 (m.d 0 2) (by simp) with h193 | h193
                                          · linarith only [h193, h4, hlam]
                                          · linarith only [h100, h193, hlam]
                                        · linarith only [h192, h3, hlam]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h2, hlam, p173_1]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h0, h127, h171, h172, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p173_1, u1elo0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h0, h127, h171, h172, h2, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p173_1, u1elo0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        rcases p173_3 (m.d 0 1) (by simp) with h201 | h201
                                        · rcases p173_3 (m.d 0 2) (by simp) with h202 | h202
                                          · linarith only [h202, h74, hlam]
                                          · linarith only [h100, h202, hlam]
                                        · linarith only [h201, h3, hlam]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h3, hlam, p173_1]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h100, hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h123, hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [h124, hlam, p173_0]
                                      · have p173_0 := h173c.1
                                        have p173_1 := h173c.2.1
                                        have p173_2 := h173c.2.2.1
                                        have p173_3 := h173c.2.2.2
                                        linarith only [hlam, p173_0]
                                    · linarith only [h132, h172, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h0, h127, h171, h4, hc25, hlam, hphi, u5elo3]
                              · linarith only [h131, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h130, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h127, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h124, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h123, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h100, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
        · rcases m.htr 0 2 3 (by decide) (by decide) with h221 | h221
          · rcases m.htr 0 2 4 (by decide) (by decide) with h222 | h222
            · linarith only [h0, h2, h222, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h224 | h224
              · rcases m.htr 0 3 4 (by decide) (by decide) with h225 | h225
                · linarith only [h1, h2, h225, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h227 | h227
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
                      · linarith only [h0, h2, h229, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · linarith only [h0, h2, h221, h229, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h2, h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h227, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h221, h224, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h235 | h235
            · linarith only [h1, h2, h221, h235, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h237 | h237
              · rcases m.htr 0 3 4 (by decide) (by decide) with h238 | h238
                · linarith only [h1, h2, h238, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h240 | h240
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                      · linarith only [h0, h221, h242, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h244 | h244
                        · linarith only [h1, h2, h242, h244, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h221, h237, h244, hc12, hc23, hlam, hphi]
                    · linarith only [h241, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h221, h240, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h237, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h220, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h251 | h251
      · rcases m.htr 0 1 5 (by decide) (by decide) with h252 | h252
        · rcases m.htr 0 2 3 (by decide) (by decide) with h253 | h253
          · linarith only [h0, h1, h253, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h255 | h255
            · rcases m.htr 0 2 5 (by decide) (by decide) with h256 | h256
              · rcases m.htr 0 3 4 (by decide) (by decide) with h257 | h257
                · rcases m.htr 0 3 5 (by decide) (by decide) with h258 | h258
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                      · linarith only [h0, h253, h260, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h0, h1, h262, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h262, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h259, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h258, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1, h251, h257, hlam]
              · linarith only [h255, h256, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
              · rcases m.htr 0 3 4 (by decide) (by decide) with h270 | h270
                · rcases m.htr 0 3 5 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h272 | h272
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
                      · linarith only [h253, h269, h273, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                        · linarith only [h0, h1, h275, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h255, h269, h275, hc12, hc24, hlam, hphi]
                    · linarith only [h255, h272, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1, h271, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h1, h251, h270, hlam]
              · linarith only [h269, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h252, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h283 | h283
        · rcases m.htr 0 2 3 (by decide) (by decide) with h284 | h284
          · linarith only [h0, h1, h284, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h286 | h286
            · linarith only [h0, h251, h286, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 3 4 (by decide) (by decide) with h289 | h289
                · rcases m.htr 0 3 5 (by decide) (by decide) with h290 | h290
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h291 | h291
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                      · linarith only [h0, h284, h292, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                        · linarith only [h0, h251, h294, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h294, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h291, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h290, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h299 | h299
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h300 | h300
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
                      · linarith only [h284, h288, h301, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
                        · linarith only [h0, h1, h303, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h303, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h300, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h299, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h288, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h283, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
    · rcases m.htr 0 1 4 (by decide) (by decide) with h311 | h311
      · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
        · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
          · rcases m.htr 0 2 4 (by decide) (by decide) with h314 | h314
            · rcases m.htr 0 2 5 (by decide) (by decide) with h315 | h315
              · rcases m.htr 0 3 4 (by decide) (by decide) with h316 | h316
                · rcases m.htr 0 3 5 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                          · linarith only [h0, h310, h321, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h0, h310, h316, h319, h321, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h0, h320, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h313, h319, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h318, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h316, h317, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h328 | h328
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                          · linarith only [h0, h310, h316, h328, h332, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                            · linarith only [h0, h311, h332, h334, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h316, h328, h330, h334, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h331, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h313, h330, hlam]
                    · linarith only [h316, h328, h329, hc35, hlam, hphi, u5elo4]
                  · linarith only [h328, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h315, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h311, h314, hlam]
          · linarith only [h0, h310, h313, hlam]
        · linarith only [h310, h312, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h345 | h345
        · rcases m.htr 0 2 3 (by decide) (by decide) with h346 | h346
          · rcases m.htr 0 2 4 (by decide) (by decide) with h347 | h347
            · rcases m.htr 0 2 5 (by decide) (by decide) with h348 | h348
              · rcases m.htr 0 3 4 (by decide) (by decide) with h349 | h349
                · linarith only [h310, h311, h349, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                          · linarith only [h310, h349, h355, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h357 | h357
                            · linarith only [h0, h310, h357, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h353, h357, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h354, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h310, h346, h353, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h352, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h346, h351, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h348, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h365 | h365
              · rcases m.htr 0 3 4 (by decide) (by decide) with h366 | h366
                · linarith only [h0, h310, h347, h366, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h368 | h368
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                          · linarith only [h310, h366, h372, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                            · linarith only [h310, h311, h374, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                            · linarith only [h374, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h371, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h311, h346, h347, h370, hc01, hlam, hphi, u1elo3]
                    · linarith only [h347, h369, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h368, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h310, h365, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h310, h346, hlam]
        · linarith only [h310, h345, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h384 | h384
      · rcases m.htr 0 1 5 (by decide) (by decide) with h385 | h385
        · rcases m.htr 0 2 3 (by decide) (by decide) with h386 | h386
          · rcases m.htr 0 2 4 (by decide) (by decide) with h387 | h387
            · rcases m.htr 0 2 5 (by decide) (by decide) with h388 | h388
              · rcases m.htr 0 3 4 (by decide) (by decide) with h389 | h389
                · rcases m.htr 0 3 5 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h396 | h396
                              · linarith only [h310, h384, h392, h396, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · linarith only [h396, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h310, h395, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h310, h386, h389, h394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h310, h392, h393, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h386, h392, hlam]
                    · linarith only [h391, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h390, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h310, h384, h389, hlam]
              · linarith only [h388, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h310, h384, h386, h387, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h408 | h408
            · rcases m.htr 0 2 5 (by decide) (by decide) with h409 | h409
              · rcases m.htr 0 3 4 (by decide) (by decide) with h410 | h410
                · rcases m.htr 0 3 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h412 | h412
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
                      · linarith only [h386, h408, h413, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
                              · linarith only [h0, h384, h418, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · linarith only [h418, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h413, h417, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h410, h413, h416, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h384, h415, hc14, hlam, hphi, ht45, u5elo2]
                    · linarith only [h412, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h411, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h384, h386, h410, hlam]
              · linarith only [h0, h384, h409, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h384, h408, hlam]
        · linarith only [h384, h385, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h430 | h430
        · rcases m.htr 0 2 3 (by decide) (by decide) with h431 | h431
          · rcases m.htr 0 2 4 (by decide) (by decide) with h432 | h432
            · rcases m.htr 0 2 5 (by decide) (by decide) with h433 | h433
              · rcases m.htr 0 3 4 (by decide) (by decide) with h434 | h434
                · rcases m.htr 0 3 5 (by decide) (by decide) with h435 | h435
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h438 | h438
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h439 | h439
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h440 | h440
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h441 | h441
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h443 | h443
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h444 | h444
                                    · linarith only [h431, h442, h444, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h444, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h443, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                                  · linarith only [h434, h442, h448, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h448, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h384, h441, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h384, h430, h438, h439, h440, hc25, hlam, hphi, u5elo3]
                          · linarith only [h310, h434, h439, hlam]
                        · linarith only [h0, h438, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h430, h431, h437, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h384, h430, h436, hc15, hlam, hphi, u5elo4]
                  · linarith only [h435, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                          · linarith only [h310, h430, h434, h461, h462, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h464 | h464
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                                · linarith only [h310, h430, h431, h461, h462, h466, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
                                    · rcases h0bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h310, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h384, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h310, hc05, hlam, hphi, ht01, ht0b, ht5b, p470_1, u1elo2]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, p470_1, u1elo1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h310, h430, h461, h468, h469, hc45, hlam, hphi, ht01, ht0b, ht5b, p470_1, u1elo1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h384, h430, h461, h468, h469, hc45, hlam, hphi, ht01, ht0b, ht5b, p470_1, u1elo1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        rcases p470_3 (m.d 0 1) (by simp) with h480 | h480
                                        · linarith only [h0, h480, hlam]
                                        · linarith only [h430, h480, hlam]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h430, h461, h468, h469, hc45, hlam, hphi, ht0b, ht5b, p470_1, u0elo2]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h431, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h434, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        rcases p470_3 (m.d 0 1) (by simp) with h487 | h487
                                        · linarith only [h310, h487, hlam]
                                        · linarith only [h430, h487, hlam]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h430, h432, h461, h468, h469, hc45, hlam, hphi, ht01, ht0b, ht5b, p470_1, u1elo1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h432, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h0, h310, h430, h432, h461, h468, h469, hc45, hlam, hphi, ht01, ht0b, ht5b, p470_1, u1elo1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        rcases p470_3 (m.d 0 1) (by simp) with h494 | h494
                                        · linarith only [h384, h494, hlam]
                                        · linarith only [h430, h494, hlam]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h430, hlam, p470_1]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h433, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h458, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [h459, hlam, p470_0]
                                      · have p470_0 := h470c.1
                                        have p470_1 := h470c.2.1
                                        have p470_2 := h470c.2.2.1
                                        have p470_3 := h470c.2.2.2
                                        linarith only [hlam, p470_0]
                                    · linarith only [h462, h469, hc13, hlam, hphi, ht34, ht45, u5elo4]
                                  · linarith only [h468, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h465, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h310, h464, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h461, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h431, h460, hlam]
                    · linarith only [h434, h459, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h310, h430, h458, hc15, hlam, hphi, u5elo3]
              · linarith only [h433, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h511 | h511
              · rcases m.htr 0 3 4 (by decide) (by decide) with h512 | h512
                · linarith only [h431, h432, h512, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h514 | h514
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h515 | h515
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h518 | h518
                          · linarith only [h310, h430, h512, h516, h517, h518, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h520 | h520
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                                · linarith only [h310, h430, h517, h518, h522, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h525 | h525
                                    · rcases h0bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h0, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h310, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h384, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h310, h518, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h430, h432, hc15, hlam, hphi, ht0b, ht5b, p526_1, u0elo3]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h310, h430, h432, h517, h524, h525, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p526_1]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h432, hlam, p526_1]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        rcases p526_3 (m.d 0 1) (by simp) with h536 | h536
                                        · linarith only [h0, h536, hlam]
                                        · linarith only [h430, h536, hlam]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h430, h517, h524, h525, hc45, hlam, hphi, ht0b, ht5b, p526_1, u0elo2]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h431, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h512, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        rcases p526_3 (m.d 0 1) (by simp) with h543 | h543
                                        · linarith only [h310, h543, hlam]
                                        · linarith only [h430, h543, hlam]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h384, h430, h517, h524, h525, hc45, hlam, hphi, ht01, ht0b, ht5b, p526_1, u1elo3]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h0, h384, h430, h517, h524, h525, hc45, hlam, hphi, ht01, ht0b, ht5b, p526_1, u1elo3]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h310, h384, h430, h517, h524, h525, hc45, hlam, hphi, ht01, ht0b, ht5b, p526_1, u1elo3]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        rcases p526_3 (m.d 0 1) (by simp) with h550 | h550
                                        · linarith only [h384, h550, hlam]
                                        · linarith only [h430, h550, hlam]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h430, hlam, p526_1]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h511, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h514, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [h515, hlam, p526_0]
                                      · have p526_0 := h526c.1
                                        have p526_1 := h526c.2.1
                                        have p526_2 := h526c.2.2.1
                                        have p526_3 := h526c.2.2.2
                                        linarith only [hlam, p526_0]
                                    · linarith only [h310, h430, h517, h518, h524, h525, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h524, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h384, h521, hc04, hlam, hphi, ht45, u5elo4]
                            · linarith only [h310, h430, h517, h520, hc25, hlam, hphi, u5elo3]
                        · linarith only [h517, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h431, h516, hlam]
                    · linarith only [h515, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h310, h514, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h511, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h567 | h567
            · rcases m.htr 0 2 5 (by decide) (by decide) with h568 | h568
              · rcases m.htr 0 3 4 (by decide) (by decide) with h569 | h569
                · rcases m.htr 0 3 5 (by decide) (by decide) with h570 | h570
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h571 | h571
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
                      · linarith only [h384, h430, h431, h567, h572, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h574 | h574
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h580 | h580
                                    · rcases h0bigk with h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h0, hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h310, hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h384, hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h0, h430, h572, h574, h579, h580, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p581_1]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h0, h572, hc01, hc23, hlam, hphi, ht12, p581_1]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h431, hlam, p581_1]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h0, h384, h430, h572, h574, h579, h580, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p581_1]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        rcases p581_3 (m.d 0 1) (by simp) with h591 | h591
                                        · linarith only [h0, h591, hlam]
                                        · linarith only [h430, h591, hlam]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h430, h574, h579, h580, hc45, hlam, hphi, ht0b, ht5b, p581_1, u0elo2]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h0, h310, h430, h574, h579, h580, hc45, hlam, hphi, ht01, ht0b, ht5b, p581_1, u1elo2]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h310, h384, h430, h574, h579, h580, hc45, hlam, hphi, ht01, ht0b, ht5b, p581_1, u1elo2]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        rcases p581_3 (m.d 0 1) (by simp) with h598 | h598
                                        · linarith only [h310, h598, hlam]
                                        · linarith only [h430, h598, hlam]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h430, h574, h579, h580, hc45, hlam, hphi, ht0b, ht5b, p581_1, u0elo3]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h567, hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h569, hlam, p581_1]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        rcases p581_3 (m.d 0 1) (by simp) with h605 | h605
                                        · linarith only [h384, h605, hlam]
                                        · linarith only [h430, h605, hlam]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h430, hlam, p581_1]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h568, hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h570, hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [h571, hlam, p581_0]
                                      · have p581_0 := h581c.1
                                        have p581_1 := h581c.2.1
                                        have p581_2 := h581c.2.2.1
                                        have p581_3 := h581c.2.2.2
                                        linarith only [hlam, p581_0]
                                    · linarith only [h580, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h572, h579, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h0, h430, h572, h574, h578, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h577, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h310, h576, hc03, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h430, h569, h572, h574, h575, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h0, h574, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h384, h430, h571, hc15, hlam, hphi, u5elo4]
                  · linarith only [h570, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h431, h567, h569, hlam]
              · linarith only [h384, h567, h568, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h624 | h624
              · rcases m.htr 0 3 4 (by decide) (by decide) with h625 | h625
                · rcases m.htr 0 3 5 (by decide) (by decide) with h626 | h626
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h627 | h627
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
                      · linarith only [h0, h430, h431, h628, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h631 | h631
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h632 | h632
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h633 | h633
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h635 | h635
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h636 | h636
                                    · rcases h0bigk with h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h0, hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h310, hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h384, hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h0, h628, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p637_1]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h567, hc01, hc24, hlam, hphi, ht12, p637_1]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h431, hlam, p637_1]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h567, hlam, p637_1]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        rcases p637_3 (m.d 0 1) (by simp) with h647 | h647
                                        · linarith only [h0, h647, hlam]
                                        · linarith only [h430, h647, hlam]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h430, h630, h635, h636, hc45, hlam, hphi, ht0b, ht5b, p637_1, u0elo2]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h0, h310, h430, h630, h635, h636, hc45, hlam, hphi, ht01, ht0b, ht5b, p637_1, u1elo2]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h310, h384, h430, h630, h635, h636, hc45, hlam, hphi, ht01, ht0b, ht5b, p637_1, u1elo2]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        rcases p637_3 (m.d 0 1) (by simp) with h654 | h654
                                        · linarith only [h310, h654, hlam]
                                        · linarith only [h430, h654, hlam]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h430, h630, h635, h636, hc45, hlam, hphi, ht0b, ht5b, p637_1, u0elo3]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h0, h384, h430, h630, h631, h635, h636, hc45, hlam, hphi, ht01, ht0b, ht5b, p637_1, u1elo2]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h625, hlam, p637_1]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        rcases p637_3 (m.d 0 1) (by simp) with h661 | h661
                                        · linarith only [h384, h661, hlam]
                                        · linarith only [h430, h661, hlam]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h430, hlam, p637_1]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h624, hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h626, hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [h627, hlam, p637_0]
                                      · have p637_0 := h637c.1
                                        have p637_1 := h637c.2.1
                                        have p637_2 := h637c.2.2.1
                                        have p637_3 := h637c.2.2.2
                                        linarith only [hlam, p637_0]
                                    · linarith only [h636, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h628, h635, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h0, h430, h628, h630, h634, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h384, h633, hc04, hlam, hphi, ht45, u5elo4]
                            · linarith only [h310, h632, hc03, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h310, h625, h631, hlam]
                        · linarith only [h0, h430, h630, hc15, hlam, hphi, u5elo2]
                    · linarith only [h567, h627, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h430, h567, h625, h626, hc15, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h678 | h678
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h680 | h680
                      · linarith only [h0, h430, h431, h680, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h682 | h682
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h683 | h683
                          · linarith only [h625, h678, h683, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h685 | h685
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h686 | h686
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h687 | h687
                                · linarith only [h0, h430, h680, h682, h683, h687, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h430, h680, h682, h687, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h430, h680, h682, h683, h686, hc25, hlam, hphi, u5elo4]
                            · linarith only [h0, h430, h680, h682, h685, hc25, hlam, hphi, u5elo3]
                        · linarith only [h0, h430, h682, hc15, hlam, hphi, u5elo2]
                    · linarith only [h679, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h431, h678, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h430, h624, hc15, hlam, hphi, u5elo2]
        · linarith only [h430, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT1_M_LI_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 2 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h3, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h0, h10, h3, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h3, h5, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h14, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · linarith only [h0, h14, h3, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h17, h3, h6, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h19, h3, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h21, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · linarith only [h0, h21, h3, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h24 | h24
              · linarith only [h2, h24, h3, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h26 | h26
                · linarith only [h26, h5, h6, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h2, h28, h3, h5, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
                    · linarith only [h2, h3, h30, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                      · linarith only [h0, h3, h32, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · linarith only [h2, h3, h32, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h35 | h35
            · rcases m.htr 0 2 5 (by decide) (by decide) with h36 | h36
              · linarith only [h36, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h38 | h38
                · rcases m.htr 0 3 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h1, h3, h39, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h1, h3, h35, h41, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                      · linarith only [h35, h43, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                        · linarith only [h1, h3, h43, h45, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h35, h45, h5, hc12, hc23, hlam, hphi]
                · linarith only [h35, h38, h5, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
              · linarith only [h1, h3, h49, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
                  · linarith only [h1, h3, h52, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h1, h3, h51, h54, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
                      · linarith only [h0, h3, h56, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                        · linarith only [h1, h3, h35, h56, h58, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                          · linarith only [h0, h49, h60, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                            · linarith only [h1, h3, h62, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                            · linarith only [h1, h3, h51, h56, h62, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h2, h3, h51, h65, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                    · linarith only [h2, h3, h67, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                      · linarith only [h0, h3, h5, h69, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                        · linarith only [h1, h35, h51, h69, h71, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                          · linarith only [h0, h73, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                            · linarith only [h1, h3, h75, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                              · linarith only [h2, h3, h65, h75, h77, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                                · linarith only [h2, h3, h5, h51, h67, h79, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                                    · linarith only [h0, h3, h79, h82, hc12, hc24, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                                      · linarith only [h0, h35, h82, h84, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h0bigk with h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [hlam, p86_0]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p86_1, u1elo4]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h0, h3, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p86_1, u1elo4]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h0, h3, h5, h51, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p86_1, u1elo4]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h3, hlam, p86_0]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h0, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [hlam, p86_0]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h5, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h35, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h49, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h1, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h0, h1, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p86_1, u1elo4]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [hlam, p86_0]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h51, hlam, p86_0]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h65, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h2, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p86_1, u1elo4]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h2, h3, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p86_1, u1elo4]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [hlam, p86_0]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h67, hlam, p86_1]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [h1, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p86_1, u0elo4]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          rcases p86_3 (m.d 0 1) (by simp) with h108 | h108
                                          · linarith only [h108, h3, hlam]
                                          · linarith only [h0, h108, hlam]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          rcases p86_3 (m.d 0 1) (by simp) with h111 | h111
                                          · linarith only [h111, h3, hlam]
                                          · linarith only [h1, h111, hlam]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          rcases p86_3 (m.d 0 1) (by simp) with h114 | h114
                                          · linarith only [h114, h3, hlam]
                                          · linarith only [h114, h2, hlam]
                                        · have p86_0 := h86c.1
                                          have p86_1 := h86c.2.1
                                          have p86_2 := h86c.2.2.1
                                          have p86_3 := h86c.2.2.2
                                          linarith only [hlam, p86_0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                                    · linarith only [h118, h2, h3, h69, h75, h79, hc12, hc24, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h120 | h120
                                      · linarith only [h0, h118, h120, h35, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h0, h120, h5, h81, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h123 | h123
        · linarith only [h123, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h125 | h125
          · rcases m.htr 0 2 4 (by decide) (by decide) with h126 | h126
            · linarith only [h0, h126, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h128 | h128
              · linarith only [h0, h128, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
                · linarith only [h1, h130, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h125, h132, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                    · linarith only [h134, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
                      · linarith only [h0, h136, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · linarith only [h0, h125, h136, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h139 | h139
            · linarith only [h1, h125, h139, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h141 | h141
              · linarith only [h1, h125, h141, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h143 | h143
                · linarith only [h1, h143, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
                  · linarith only [h1, h145, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
                    · linarith only [h147, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
                      · linarith only [h0, h125, h149, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                        · linarith only [h0, h139, h151, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                          · linarith only [h1, h141, h149, h153, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                            · linarith only [h1, h143, h155, h2, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                              · linarith only [h1, h145, h157, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                                · linarith only [h159, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                                · linarith only [h1, h149, h159, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h162 | h162
      · rcases m.htr 0 1 5 (by decide) (by decide) with h163 | h163
        · linarith only [h1, h163, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h165 | h165
          · linarith only [h0, h1, h165, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h167 | h167
            · rcases m.htr 0 2 5 (by decide) (by decide) with h168 | h168
              · linarith only [h0, h1, h168, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h170 | h170
                · rcases m.htr 0 3 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h171, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h173, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
                      · linarith only [h0, h1, h165, h175, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                        · linarith only [h0, h1, h177, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h167, h177, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h0, h1, h167, h170, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h181 | h181
              · linarith only [h1, h162, h167, h181, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 0 3 5 (by decide) (by decide) with h184 | h184
                  · linarith only [h184, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                    · linarith only [h1, h162, h186, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
                      · linarith only [h0, h1, h188, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                        · linarith only [h0, h1, h167, h190, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                          · linarith only [h0, h181, h192, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h195 | h195
                              · linarith only [h195, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                              · linarith only [h1, h162, h190, h195, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h162, h190, h194, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h162, h183, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
        · linarith only [h1, h200, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h202 | h202
          · linarith only [h0, h1, h202, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h204 | h204
            · linarith only [h0, h162, h204, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h206 | h206
              · linarith only [h0, h1, h206, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
                · rcases m.htr 0 3 5 (by decide) (by decide) with h209 | h209
                  · linarith only [h209, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
                    · linarith only [h211, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                      · linarith only [h0, h1, h202, h213, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                        · linarith only [h0, h1, h204, h215, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                          · linarith only [h0, h206, h217, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                              · linarith only [h162, h208, h209, h220, hc01, hlam, hphi, u1elo2]
                              · linarith only [h0, h1, h220, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h219, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h224 | h224
                  · linarith only [h224, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h226 | h226
                    · linarith only [h162, h226, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
                      · linarith only [h0, h202, h228, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                        · linarith only [h0, h200, h204, h208, h230, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h0, h200, h206, h232, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                            · linarith only [h1, h208, h234, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h1, h234, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h237 | h237
    · rcases m.htr 0 1 4 (by decide) (by decide) with h238 | h238
      · rcases m.htr 0 1 5 (by decide) (by decide) with h239 | h239
        · linarith only [h239, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h241 | h241
          · rcases m.htr 0 2 4 (by decide) (by decide) with h242 | h242
            · rcases m.htr 0 2 5 (by decide) (by decide) with h243 | h243
              · linarith only [h0, h243, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h245 | h245
                · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
                  · linarith only [h0, h237, h246, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h248 | h248
                    · linarith only [h0, h237, h245, h248, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h251 | h251
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h252 | h252
                          · linarith only [h252, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h254 | h254
                            · linarith only [h0, h237, h252, h254, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h237, h245, h252, h254, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h242, h251, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h239, h241, h243, h250, hc01, hlam, hphi, u1elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h259 | h259
                  · linarith only [h238, h245, h259, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
                    · linarith only [h0, h238, h261, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h264 | h264
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                          · linarith only [h265, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h267 | h267
                            · linarith only [h0, h237, h245, h265, h267, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h269 | h269
                              · linarith only [h237, h259, h269, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h271 | h271
                                · linarith only [h0, h238, h245, h261, h265, h271, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h273 | h273
                                  · linarith only [h237, h245, h263, h273, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h275 | h275
                                    · linarith only [h0, h238, h264, h265, h271, h275, hlam]
                                    · linarith only [h0, h238, h265, h275, hc14, hc45, hlam, hphi]
                        · linarith only [h0, h237, h242, h263, h264, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h241, h263, hlam]
            · linarith only [h0, h238, h242, hlam]
          · linarith only [h0, h237, h241, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h282 | h282
        · linarith only [h282, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h284 | h284
          · rcases m.htr 0 2 4 (by decide) (by decide) with h285 | h285
            · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
              · linarith only [h0, h286, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
                · linarith only [h237, h238, h288, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h0, h237, h290, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h292 | h292
                    · linarith only [h292, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h296 | h296
                          · linarith only [h285, h286, h296, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                            · linarith only [h237, h238, h288, h295, h296, h298, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                              · linarith only [h237, h290, h300, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h302 | h302
                                · linarith only [h295, h296, h302, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · linarith only [h237, h238, h302, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h237, h285, h294, h295, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h284, h294, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h307 | h307
              · linarith only [h307, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h309 | h309
                · linarith only [h0, h237, h285, h309, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h311 | h311
                  · linarith only [h237, h311, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h313 | h313
                    · linarith only [h238, h313, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
                        · linarith only [h0, h285, h316, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
                          · linarith only [h307, h316, h318, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h320 | h320
                            · linarith only [h0, h237, h316, h320, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                              · linarith only [h0, h237, h311, h316, h322, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                                · linarith only [h324, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                                · linarith only [h237, h238, h315, h324, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h284, h315, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h237, h284, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h329 | h329
      · rcases m.htr 0 1 5 (by decide) (by decide) with h330 | h330
        · linarith only [h0, h330, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h332 | h332
          · rcases m.htr 0 2 4 (by decide) (by decide) with h333 | h333
            · rcases m.htr 0 2 5 (by decide) (by decide) with h334 | h334
              · linarith only [h334, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h336 | h336
                · rcases m.htr 0 3 5 (by decide) (by decide) with h337 | h337
                  · linarith only [h337, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                    · linarith only [h0, h329, h339, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h343 | h343
                          · linarith only [h332, h334, h343, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
                              · linarith only [h337, h341, h343, h346, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h348 | h348
                                · linarith only [h329, h339, h348, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
                                    · linarith only [h237, h329, h342, h346, h348, h351, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                    · linarith only [h332, h334, h350, h351, hc34, hc45, hlam, hphi]
                                  · linarith only [h237, h336, h346, h350, hc23, hc35, hlam, hphi]
                            · linarith only [h237, h329, h336, h345, hlam]
                        · linarith only [h237, h329, h333, h341, h342, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h329, h332, h341, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h237, h329, h336, hlam]
            · linarith only [h0, h329, h333, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h360 | h360
            · rcases m.htr 0 2 5 (by decide) (by decide) with h361 | h361
              · linarith only [h361, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h363 | h363
                · rcases m.htr 0 3 5 (by decide) (by decide) with h364 | h364
                  · linarith only [h237, h364, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                    · linarith only [h329, h366, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
                      · linarith only [h332, h360, h368, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h370 | h370
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                          · linarith only [h361, h368, h371, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                              · linarith only [h374, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
                                · linarith only [h329, h366, h376, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h379 | h379
                                    · linarith only [h332, h360, h364, h376, h379, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi1]
                                    · linarith only [h0, h329, h370, h371, h378, h379, hc34, hc45, hlam, hphi]
                                  · linarith only [h332, h363, h378, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h237, h329, h363, h373, hlam]
                        · linarith only [h0, h360, h370, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h329, h332, h363, hlam]
            · linarith only [h0, h329, h360, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h387 | h387
        · linarith only [h0, h387, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h389 | h389
          · rcases m.htr 0 2 4 (by decide) (by decide) with h390 | h390
            · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
              · linarith only [h391, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h393 | h393
                · rcases m.htr 0 3 5 (by decide) (by decide) with h394 | h394
                  · linarith only [h394, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h396 | h396
                    · linarith only [h396, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                          · linarith only [h389, h391, h400, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h402 | h402
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
                              · linarith only [h393, h394, h398, h400, h403, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                                · linarith only [h396, h402, h403, h405, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                                    · linarith only [h390, h393, h408, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · linarith only [h0, h389, h400, h407, h408, hc34, hc45, hlam, hphi]
                                  · linarith only [h237, h393, h403, h407, hc23, hc35, hlam, hphi]
                            · linarith only [h237, h393, h402, hlam]
                        · linarith only [h0, h390, h399, hlam]
                      · linarith only [h0, h389, h398, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
                  · linarith only [h390, h393, h415, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h417 | h417
                    · linarith only [h387, h390, h391, h417, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h421 | h421
                          · linarith only [h389, h391, h421, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                            · linarith only [h237, h393, h423, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h425 | h425
                              · linarith only [h415, h420, h421, h423, h425, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                                · linarith only [h420, h421, h427, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                                  · linarith only [h389, h393, h429, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h431 | h431
                                    · linarith only [h390, h391, h423, h427, h431, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                                      · linarith only [h0, h421, h431, h433, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · linarith only [h237, h423, h433, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h390, h420, hlam]
                      · linarith only [h0, h237, h389, h419, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h438 | h438
              · linarith only [h329, h390, h438, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h440 | h440
                · linarith only [h389, h390, h440, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h442 | h442
                  · linarith only [h329, h389, h390, h442, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
                    · linarith only [h329, h444, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h447 | h447
                        · linarith only [h389, h390, h447, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                          · linarith only [h438, h447, h449, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                            · linarith only [h237, h440, h446, h447, h451, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
                              · linarith only [h442, h451, h453, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h455 | h455
                                · linarith only [h389, h390, h444, h455, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                                  · linarith only [h0, h389, h447, h455, h457, hc34, hc45, hlam, hphi]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                                    · linarith only [h329, h389, h390, h455, h457, h459, hc23, hc34, hlam, hphi]
                                    · linarith only [h389, h390, h459, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h389, h390, h446, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h463 | h463
            · rcases m.htr 0 2 5 (by decide) (by decide) with h464 | h464
              · linarith only [h464, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 3 5 (by decide) (by decide) with h467 | h467
                  · linarith only [h237, h467, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h469 | h469
                    · linarith only [h389, h463, h467, h469, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                      · linarith only [h0, h389, h471, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
                          · linarith only [h463, h464, h474, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h476 | h476
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                              · linarith only [h389, h463, h467, h477, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                                · linarith only [h469, h479, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h481 | h481
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h482 | h482
                                    · linarith only [h463, h479, h482, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h484 | h484
                                      · linarith only [h0, h474, h482, h484, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · rcases h0bigk with h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h0, hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h237, hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h329, hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h387, hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, p486_1, u1elo1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h389, hlam, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h0, h329, h474, hc01, hc25, hlam, hphi, ht12, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h464, hlam, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h237, h477, h484, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h237, h477, h484, hc02, hc45, hlam, hphi, ht23, ht34, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h237, h329, h477, h484, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h467, hlam, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h329, hc01, hlam, hphi, p486_1, u1elo3]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h463, hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h466, hlam, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [hlam, p486_0]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h469, hlam, p486_1]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h387, hc01, hlam, hphi, p486_1, u1elo4]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h387, h463, h481, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p486_1, u1elo4]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h237, h387, hc01, hlam, hphi, p486_1, u1elo4]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [h329, h387, hc01, hlam, hphi, p486_1, u1elo4]
                                        · have p486_0 := h486c.1
                                          have p486_1 := h486c.2.1
                                          have p486_2 := h486c.2.2.1
                                          have p486_3 := h486c.2.2.2
                                          linarith only [hlam, p486_0]
                                  · linarith only [h389, h466, h481, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h237, h329, h466, h471, h473, h476, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h389, h463, h467, h473, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h389, h463, h466, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h516 | h516
              · linarith only [h516, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h518 | h518
                · rcases m.htr 0 3 5 (by decide) (by decide) with h519 | h519
                  · linarith only [h237, h519, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h521 | h521
                    · linarith only [h518, h519, h521, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                      · linarith only [h0, h389, h523, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
                        · linarith only [h0, h463, h523, h525, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h527 | h527
                          · linarith only [h516, h523, h527, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h529 | h529
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h530 | h530
                              · linarith only [h530, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h532 | h532
                                · linarith only [h521, h529, h530, h532, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h534 | h534
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h535 | h535
                                    · linarith only [h0, h525, h532, h535, hc01, hc24, hlam, hphi, ht12]
                                    · linarith only [h0, h525, h535, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h237, h518, h530, h534, hc23, hc35, hlam, hphi]
                            · linarith only [h237, h518, h529, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h540 | h540
                  · linarith only [h518, h540, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h542 | h542
                    · linarith only [h329, h542, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                      · linarith only [h0, h389, h544, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                        · linarith only [h0, h463, h544, h546, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                          · linarith only [h516, h544, h548, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
                            · linarith only [h237, h518, h550, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h552 | h552
                              · linarith only [h540, h550, h552, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h554 | h554
                                · linarith only [h554, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                                  · linarith only [h0, h544, h550, h556, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h544, h556, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT1_M_LI_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h5ehi := hb5.2.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h11, h14, h3, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h0, h13, h14, h4, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                          · linarith only [h0, h13, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h10, h5, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h4, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h0, h22, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                            · linarith only [h1, h25, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h0, h24, h25, h4, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h24, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h20, h21, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h20, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h31, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h0, h35, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                            · linarith only [h1, h38, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                              · linarith only [h2, h31, h40, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                                · linarith only [h3, h33, h35, h42, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h42, h6, h7, hc23, hc35, hlam, hphi]
                          · linarith only [h37, h6, h7, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h34, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h33, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
                · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                        · linarith only [h0, h52, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                          · linarith only [h48, h54, h6, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                            · linarith only [h3, h51, h52, h54, h56, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h48, h56, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                      · linarith only [h0, h5, h50, h51, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h4, h50, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · linarith only [h48, h49, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h0, h65, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                          · linarith only [h3, h6, h63, h65, h67, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                            · linarith only [h1, h69, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h71 | h71
                              · linarith only [h3, h64, h65, h71, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h0, h5, h62, h67, h71, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h0, h5, h63, h64, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h4, h63, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h0, h78, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                          · linarith only [h1, h6, h80, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                            · linarith only [h1, h48, h82, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                              · linarith only [h3, h62, h77, h78, h84, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                                · linarith only [h1, h3, h6, h76, h78, h86, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                                  · linarith only [h3, h48, h77, h78, h86, h88, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                                    · linarith only [h3, h62, h77, h78, h90, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                                      · linarith only [h77, h78, h86, h90, h92, hc23, hc34, hlam, hphi]
                                      · linarith only [h1, h6, h92, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h0, h5, h77, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                    · linarith only [h0, h4, h76, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
              · linarith only [h4, h5, h97, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
                · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
                      · linarith only [h102, h4, h5, h99, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                        · linarith only [h102, h104, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                          · linarith only [h101, h102, h106, h2, h97, h99, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                            · linarith only [h101, h102, h108, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h108, h4, h99, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                    · linarith only [h101, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h100, h4, h5, h99, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                      · linarith only [h0, h115, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                        · linarith only [h115, h117, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                          · linarith only [h1, h119, h97, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h1, h121, h99, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                              · linarith only [h123, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h113, h114, h115, h123, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi2]
                    · linarith only [h114, h4, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                      · linarith only [h0, h128, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                        · linarith only [h128, h130, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                          · linarith only [h1, h132, h97, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                            · linarith only [h1, h134, h99, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                              · linarith only [h113, h136, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                                · linarith only [h1, h127, h128, h136, h138, h3, h97, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                                  · linarith only [h1, h127, h128, h136, h140, h3, h99, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                                    · linarith only [h113, h127, h128, h138, h142, h2, hc23, hc34, hlam, hphi]
                                    · linarith only [h1, h142, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h127, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h146 | h146
            · rcases m.htr 0 3 4 (by decide) (by decide) with h147 | h147
              · rcases m.htr 0 3 5 (by decide) (by decide) with h148 | h148
                · rcases m.htr 0 4 5 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                    · linarith only [h146, h149, h150, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                        · linarith only [h1, h150, h153, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                            · linarith only [h1, h156, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h148, h150, h152, h156, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi3]
                          · linarith only [h1, h147, h150, h152, h155, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h146, h152, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                    · linarith only [h0, h161, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h164 | h164
                        · linarith only [h1, h161, h164, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h167 | h167
                            · linarith only [h1, h167, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h1, h148, h161, h163, h167, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                          · linarith only [h1, h147, h161, h163, h166, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h146, h163, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h172 | h172
                  · linarith only [h146, h148, h172, h4, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h174 | h174
                    · linarith only [h0, h174, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h176 | h176
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h177 | h177
                        · linarith only [h0, h177, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h180 | h180
                            · linarith only [h1, h148, h180, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                              · linarith only [h172, h182, h2, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                                  · linarith only [h0, h148, h185, h4, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h146, h185, h2, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                · linarith only [h146, h184, h2, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h147, h179, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                      · linarith only [h146, h148, h176, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h146, h147, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
              · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                    · linarith only [h0, h195, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
                      · linarith only [h0, h146, h197, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                        · linarith only [h0, h199, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h202 | h202
                            · linarith only [h1, h202, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h1, h193, h201, h202, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h192, h195, h201, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
                    · linarith only [h0, h206, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                      · linarith only [h0, h146, h208, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h210 | h210
                        · linarith only [h0, h210, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h212 | h212
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h213 | h213
                            · linarith only [h1, h213, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h1, h193, h212, h213, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h192, h212, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h217 | h217
                  · linarith only [h192, h193, h217, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
                    · linarith only [h0, h219, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                      · linarith only [h0, h146, h221, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                        · linarith only [h0, h223, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
                            · linarith only [h1, h226, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
                              · linarith only [h146, h217, h225, h226, h228, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h231 | h231
                                  · linarith only [h1, h193, h231, hc23, hlam, hphi, ht12, u1ehi2]
                                  · linarith only [h0, h231, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h0, h225, h230, h4, hc13, hlam, hphi, u1ehi1]
                          · linarith only [h192, h225, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
                · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
                    · linarith only [h0, h238, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                      · linarith only [h0, h146, h240, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                        · linarith only [h0, h242, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                          · linarith only [h1, h192, h244, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                            · linarith only [h2, h244, h246, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h236, h238, h246, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
                  · linarith only [h192, h236, h237, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                    · linarith only [h0, h251, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h0, h146, h253, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                        · linarith only [h0, h255, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                          · linarith only [h0, h1, h192, h257, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h259 | h259
                            · linarith only [h1, h236, h259, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
                              · linarith only [h2, h261, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h250, h257, h261, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h264, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h146, h266, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                        · linarith only [h0, h268, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                          · linarith only [h1, h192, h270, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h272 | h272
                            · linarith only [h0, h236, h272, h4, hc13, hlam, hphi, u1ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                              · linarith only [h2, h250, h274, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                                · linarith only [h0, h192, h276, h4, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h0, h276, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h282 | h282
    · linarith only [h0, h282, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h284 | h284
      · linarith only [h0, h284, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h286 | h286
        · linarith only [h0, h286, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h288 | h288
          · rcases m.htr 0 2 4 (by decide) (by decide) with h289 | h289
            · rcases m.htr 0 3 4 (by decide) (by decide) with h290 | h290
              · rcases m.htr 0 3 5 (by decide) (by decide) with h291 | h291
                · rcases m.htr 0 4 5 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h293 | h293
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h294 | h294
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h300 | h300
                                  · linarith only [h288, h300, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h288, h291, h299, h300, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                                  · linarith only [h288, h303, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                                    · linarith only [h289, h305, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                                      · linarith only [h288, h290, h299, h305, h307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                      · linarith only [h288, h290, h292, h299, h307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h288, h290, h292, h298, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                            · linarith only [h282, h297, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h282, h296, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h282, h293, h295, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h282, h293, h294, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h293, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                              · linarith only [h284, h292, h316, h319, h321, hc12, hlam, hphi, u1ehi0]
                              · linarith only [h284, h321, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                            · linarith only [h288, h291, h320, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                          · linarith only [h282, h290, h291, h319, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                        · linarith only [h0, h318, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h289, h317, hlam]
                    · linarith only [h0, h288, h316, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
                  · linarith only [h290, h291, h329, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h333 | h333
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
                            · linarith only [h282, h291, h335, hc13, hlam, hphi, u1ehi0]
                            · linarith only [h282, h335, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h282, h290, h334, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi0]
                        · linarith only [h0, h333, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h282, h289, h331, h332, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                    · linarith only [h0, h288, h331, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h342 | h342
                · rcases m.htr 0 4 5 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                          · linarith only [h290, h342, h347, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h282, h347, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h282, h344, h346, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h289, h345, hlam]
                    · linarith only [h0, h288, h344, hlam]
                  · linarith only [h290, h342, h343, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h355 | h355
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
                          · linarith only [h282, h290, h358, hc13, hlam, hphi, u1ehi0]
                          · linarith only [h282, h358, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h0, h357, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h282, h289, h355, h356, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                    · linarith only [h0, h288, h289, h354, h355, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
                          · linarith only [h282, h290, h367, hc13, hlam, hphi, u1ehi0]
                          · linarith only [h282, h367, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h0, h366, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h282, h289, h364, h365, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                    · linarith only [h0, h288, h364, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h373 | h373
              · linarith only [h288, h289, h373, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h375 | h375
                · rcases m.htr 0 4 5 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h377 | h377
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h378 | h378
                      · linarith only [h288, h289, h375, h378, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h378, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h377, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h288, h289, h375, h376, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h383 | h383
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                      · linarith only [h0, h289, h385, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h385, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h288, h384, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                      · linarith only [h0, h289, h390, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h390, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h389, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h394 | h394
            · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
              · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
                · rcases m.htr 0 4 5 (by decide) (by decide) with h397 | h397
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                    · linarith only [h288, h394, h397, h398, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h0, h398, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
                    · linarith only [h0, h288, h401, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h401, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
                  · linarith only [h288, h394, h396, h404, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                    · linarith only [h0, h288, h406, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h406, hc23, hlam, hphi, ht12, u1ehi0]
              · linarith only [h288, h394, h395, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h410 | h410
              · rcases m.htr 0 3 5 (by decide) (by decide) with h411 | h411
                · rcases m.htr 0 4 5 (by decide) (by decide) with h412 | h412
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
                    · linarith only [h0, h288, h413, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h413, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                    · linarith only [h0, h288, h416, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h416, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h419 | h419
                  · linarith only [h410, h411, h419, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                    · linarith only [h0, h288, h421, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h421, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h424 | h424
                · rcases m.htr 0 4 5 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                    · linarith only [h0, h288, h426, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h426, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h410, h424, h425, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h430 | h430
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
                    · linarith only [h0, h288, h431, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h431, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
                    · linarith only [h0, h288, h434, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h434, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
