import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3600000 in
theorem n7l_sBT1_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
              · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h14, hlam, p0_0]
                  · linarith only [h11, h14, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, hlam, p0_0]
                  · linarith only [h11, h12, h17, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 1 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, hlam, p0_0]
                  · linarith only [h11, h21, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h24, hlam, p0_0]
                  · linarith only [h11, h24, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
              · rcases m.htr 0 1 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 0 1 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h29, hlam, p0_0]
                  · linarith only [h27, h29, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h32, hlam, p0_0]
                  · linarith only [h10, h27, h32, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
                · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h36, hlam, p0_0]
                  · linarith only [h10, h35, h36, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h39, hlam, p0_0]
                  · linarith only [h10, h39, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
                · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
                  · linarith only [h45, hlam, p0_0]
                  · linarith only [h42, h43, h45, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
                  · linarith only [h48, hlam, p0_0]
                  · linarith only [h42, h43, h48, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
                  · linarith only [h52, hlam, p0_0]
                  · linarith only [h42, h51, h52, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h55, hlam, p0_0]
                  · linarith only [h42, h55, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
              · rcases m.htr 0 1 4 (by decide) (by decide) with h59 | h59
                · rcases m.htr 0 1 5 (by decide) (by decide) with h60 | h60
                  · linarith only [h60, hlam, p0_0]
                  · linarith only [h58, h60, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h63 | h63
                  · linarith only [h63, hlam, p0_0]
                  · linarith only [h58, h63, h9, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
                · rcases m.htr 0 1 5 (by decide) (by decide) with h67 | h67
                  · linarith only [h67, hlam, p0_0]
                  · linarith only [h66, h67, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h70 | h70
                  · linarith only [h70, hlam, p0_0]
                  · linarith only [h70, h9, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h73 | h73
          · rcases p0_3 (m.d 4 5) (by simp) with h74 | h74
            · rcases m.htr 0 1 2 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h77, hlam, p0_0]
                  · linarith only [h74, h77, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h80 | h80
                  · linarith only [h80, hlam, p0_0]
                  · linarith only [h74, h75, h80, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h83 | h83
                · rcases m.htr 0 1 5 (by decide) (by decide) with h84 | h84
                  · linarith only [h84, hlam, p0_0]
                  · linarith only [h74, h83, h84, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h87 | h87
                  · linarith only [h87, hlam, p0_0]
                  · linarith only [h74, h87, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h90 | h90
              · rcases m.htr 0 1 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h92, hlam, p0_0]
                  · linarith only [h90, h92, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h95 | h95
                  · linarith only [h95, hlam, p0_0]
                  · linarith only [h73, h90, h95, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
                · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
                  · linarith only [h99, hlam, p0_0]
                  · linarith only [h73, h99, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h102 | h102
                  · linarith only [h102, hlam, p0_0]
                  · linarith only [h102, h73, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h105 | h105
            · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
              · rcases m.htr 0 1 4 (by decide) (by decide) with h107 | h107
                · rcases m.htr 0 1 5 (by decide) (by decide) with h108 | h108
                  · linarith only [h108, hlam, p0_0]
                  · linarith only [h105, h106, h108, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h111 | h111
                  · linarith only [h111, hlam, p0_0]
                  · linarith only [h105, h106, h111, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, hlam, p0_0]
                  · linarith only [h105, h114, h115, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h118 | h118
                  · linarith only [h118, hlam, p0_0]
                  · linarith only [h105, h118, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 1 4 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 1 5 (by decide) (by decide) with h123 | h123
                  · linarith only [h123, hlam, p0_0]
                  · linarith only [h121, h123, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
                  · linarith only [h126, hlam, p0_0]
                  · linarith only [h121, h126, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h129 | h129
                · rcases m.htr 0 1 5 (by decide) (by decide) with h130 | h130
                  · linarith only [h130, hlam, p0_0]
                  · linarith only [h129, h130, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h133 | h133
                  · linarith only [h133, hlam, p0_0]
                  · linarith only [h133, hc01, hc15, hlam, hphi, p0_1]
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
    rcases p0_3 (m.d 0 5) (by simp) with h138 | h138
    · linarith only [h138, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h140 | h140
      · rcases p0_3 (m.d 2 5) (by simp) with h141 | h141
        · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · rcases m.htr 0 1 2 (by decide) (by decide) with h145 | h145
              · rcases m.htr 0 1 4 (by decide) (by decide) with h146 | h146
                · rcases m.htr 0 1 5 (by decide) (by decide) with h147 | h147
                  · linarith only [h147, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h147, hc01, hc15, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h150 | h150
                  · linarith only [h138, h150, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h144, h150, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
                · rcases m.htr 0 1 5 (by decide) (by decide) with h154 | h154
                  · linarith only [h138, h154, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h144, h154, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h157 | h157
                  · linarith only [h138, h157, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h144, h157, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h160 | h160
              · rcases m.htr 0 1 4 (by decide) (by decide) with h161 | h161
                · rcases m.htr 0 1 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h138, h162, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h143, h162, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h165 | h165
                  · linarith only [h138, h165, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h143, h165, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h168 | h168
                · rcases m.htr 0 1 5 (by decide) (by decide) with h169 | h169
                  · linarith only [h138, h169, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h143, h169, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h172 | h172
                  · linarith only [h138, h168, h172, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h138, h143, h172, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h175 | h175
            · rcases m.htr 0 1 2 (by decide) (by decide) with h176 | h176
              · rcases m.htr 0 1 4 (by decide) (by decide) with h177 | h177
                · rcases m.htr 0 1 5 (by decide) (by decide) with h178 | h178
                  · linarith only [h138, h178, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h175, h178, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h181 | h181
                  · linarith only [h138, h181, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h175, h181, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h184 | h184
                · rcases m.htr 0 1 5 (by decide) (by decide) with h185 | h185
                  · linarith only [h138, h185, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h175, h185, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h188 | h188
                  · linarith only [h138, h184, h188, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h138, h175, h188, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h191 | h191
              · rcases m.htr 0 1 4 (by decide) (by decide) with h192 | h192
                · rcases m.htr 0 1 5 (by decide) (by decide) with h193 | h193
                  · linarith only [h138, h193, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h138, h193, hc01, hc15, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h196 | h196
                  · linarith only [h138, h192, h196, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h138, h196, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h199 | h199
                · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
                  · linarith only [h138, h191, h200, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h138, h200, hc01, hc15, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                  · linarith only [h138, h199, h203, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h138, h203, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h140, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h207 | h207
    · linarith only [h207, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h209 | h209
      · rcases p0_3 (m.d 2 5) (by simp) with h210 | h210
        · rcases p0_3 (m.d 3 5) (by simp) with h211 | h211
          · linarith only [h211, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases m.htr 0 1 2 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 1 4 (by decide) (by decide) with h215 | h215
                · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
                  · linarith only [h216, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h213, h216, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h219 | h219
                  · linarith only [h207, h219, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h213, h219, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h222 | h222
                · rcases m.htr 0 1 5 (by decide) (by decide) with h223 | h223
                  · linarith only [h207, h223, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h213, h223, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h226 | h226
                  · linarith only [h207, h226, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h213, h226, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h229 | h229
              · rcases m.htr 0 1 4 (by decide) (by decide) with h230 | h230
                · rcases m.htr 0 1 5 (by decide) (by decide) with h231 | h231
                  · linarith only [h207, h231, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h210, h231, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h234 | h234
                  · linarith only [h207, h234, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h210, h234, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h237 | h237
                · rcases m.htr 0 1 5 (by decide) (by decide) with h238 | h238
                  · linarith only [h207, h238, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h210, h238, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h241 | h241
                  · linarith only [h207, h241, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h210, h241, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h244 | h244
          · linarith only [h244, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · rcases m.htr 0 1 2 (by decide) (by decide) with h247 | h247
              · rcases m.htr 0 1 4 (by decide) (by decide) with h248 | h248
                · rcases m.htr 0 1 5 (by decide) (by decide) with h249 | h249
                  · linarith only [h207, h249, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h246, h249, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h252 | h252
                  · linarith only [h207, h248, h252, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h207, h246, h252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h255 | h255
                · rcases m.htr 0 1 5 (by decide) (by decide) with h256 | h256
                  · linarith only [h207, h247, h256, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h207, h246, h256, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h259 | h259
                  · linarith only [h207, h259, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h246, h259, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h262 | h262
              · rcases m.htr 0 1 4 (by decide) (by decide) with h263 | h263
                · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
                  · linarith only [h207, h264, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h264, hc01, hc15, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h267 | h267
                  · linarith only [h207, h263, h267, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h207, h267, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h270 | h270
                · rcases m.htr 0 1 5 (by decide) (by decide) with h271 | h271
                  · linarith only [h207, h271, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h207, h271, hc01, hc15, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h274 | h274
                  · linarith only [h207, h270, h274, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h207, h274, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h209, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h278 | h278
    · linarith only [h278, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h280 | h280
      · rcases p0_3 (m.d 2 5) (by simp) with h281 | h281
        · rcases p0_3 (m.d 3 5) (by simp) with h282 | h282
          · rcases p0_3 (m.d 4 5) (by simp) with h283 | h283
            · linarith only [h283, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
              · rcases m.htr 0 1 4 (by decide) (by decide) with h286 | h286
                · rcases m.htr 0 1 5 (by decide) (by decide) with h287 | h287
                  · linarith only [h287, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h282, h287, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h278, h290, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h282, h290, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h293 | h293
                · rcases m.htr 0 1 5 (by decide) (by decide) with h294 | h294
                  · linarith only [h278, h294, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h282, h294, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h278, h297, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h282, h297, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h300 | h300
            · linarith only [h300, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h302 | h302
              · rcases m.htr 0 1 4 (by decide) (by decide) with h303 | h303
                · rcases m.htr 0 1 5 (by decide) (by decide) with h304 | h304
                  · linarith only [h278, h304, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h281, h304, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h307 | h307
                  · linarith only [h278, h307, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h281, h307, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h310 | h310
                · rcases m.htr 0 1 5 (by decide) (by decide) with h311 | h311
                  · linarith only [h278, h311, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h281, h311, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h314 | h314
                  · linarith only [h278, h310, h314, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h278, h281, h314, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h317 | h317
          · rcases p0_3 (m.d 4 5) (by simp) with h318 | h318
            · linarith only [h318, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h320 | h320
              · rcases m.htr 0 1 4 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 1 5 (by decide) (by decide) with h322 | h322
                  · linarith only [h278, h322, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h317, h322, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
                  · linarith only [h278, h325, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h317, h325, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h328 | h328
                · rcases m.htr 0 1 5 (by decide) (by decide) with h329 | h329
                  · linarith only [h278, h329, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h317, h329, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h332 | h332
                  · linarith only [h278, h332, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h317, h332, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h335 | h335
            · linarith only [h335, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h337 | h337
              · rcases m.htr 0 1 4 (by decide) (by decide) with h338 | h338
                · rcases m.htr 0 1 5 (by decide) (by decide) with h339 | h339
                  · linarith only [h278, h339, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h339, hc01, hc15, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h342 | h342
                  · linarith only [h278, h338, h342, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h278, h342, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 1 5 (by decide) (by decide) with h346 | h346
                  · linarith only [h278, h346, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h278, h346, hc01, hc15, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h349 | h349
                  · linarith only [h278, h345, h349, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h278, h349, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h280, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h353 | h353
    · linarith only [h353, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h355 | h355
      · rcases p0_3 (m.d 2 5) (by simp) with h356 | h356
        · rcases p0_3 (m.d 3 5) (by simp) with h357 | h357
          · rcases p0_3 (m.d 4 5) (by simp) with h358 | h358
            · rcases m.htr 0 1 2 (by decide) (by decide) with h359 | h359
              · rcases m.htr 0 1 4 (by decide) (by decide) with h360 | h360
                · rcases m.htr 0 1 5 (by decide) (by decide) with h361 | h361
                  · linarith only [h355, h361, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h361, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h364 | h364
                  · linarith only [h355, h364, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h364, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h367 | h367
                · rcases m.htr 0 1 5 (by decide) (by decide) with h368 | h368
                  · linarith only [h355, h368, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h368, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h371 | h371
                  · linarith only [h355, h367, h371, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h371, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 1 4 (by decide) (by decide) with h375 | h375
                · rcases m.htr 0 1 5 (by decide) (by decide) with h376 | h376
                  · linarith only [h355, h376, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h376, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h379 | h379
                  · linarith only [h355, h379, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h379, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h382 | h382
                · rcases m.htr 0 1 5 (by decide) (by decide) with h383 | h383
                  · linarith only [h355, h383, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h383, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h386 | h386
                  · linarith only [h355, h386, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h386, hc01, hc25, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h389 | h389
            · rcases m.htr 0 1 2 (by decide) (by decide) with h390 | h390
              · rcases m.htr 0 1 4 (by decide) (by decide) with h391 | h391
                · rcases m.htr 0 1 5 (by decide) (by decide) with h392 | h392
                  · linarith only [h355, h392, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h392, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h395 | h395
                  · linarith only [h355, h391, h395, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h395, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h398 | h398
                · rcases m.htr 0 1 5 (by decide) (by decide) with h399 | h399
                  · linarith only [h355, h399, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h399, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h402 | h402
                  · linarith only [h355, h402, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h402, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h405 | h405
              · rcases m.htr 0 1 4 (by decide) (by decide) with h406 | h406
                · rcases m.htr 0 1 5 (by decide) (by decide) with h407 | h407
                  · linarith only [h355, h407, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h407, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h410 | h410
                  · linarith only [h355, h406, h410, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h410, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h413 | h413
                · rcases m.htr 0 1 5 (by decide) (by decide) with h414 | h414
                  · linarith only [h355, h414, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h414, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h417 | h417
                  · linarith only [h355, h413, h417, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h417, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h356, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h421 | h421
        · rcases p0_3 (m.d 3 5) (by simp) with h422 | h422
          · rcases p0_3 (m.d 4 5) (by simp) with h423 | h423
            · rcases m.htr 0 1 2 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 1 4 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 1 5 (by decide) (by decide) with h426 | h426
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h427 | h427
                    · linarith only [h427, hlam, p0_0]
                    · linarith only [h423, h427, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h355, h426, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h431 | h431
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h432 | h432
                    · linarith only [h432, hlam, p0_0]
                    · linarith only [h423, h424, h432, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h355, h431, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h436 | h436
                · rcases m.htr 0 1 5 (by decide) (by decide) with h437 | h437
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h438 | h438
                    · linarith only [h438, hlam, p0_0]
                    · linarith only [h423, h424, h438, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h355, h437, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
                    · linarith only [h443, hlam, p0_0]
                    · linarith only [h423, h424, h442, h443, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                  · linarith only [h355, h442, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h447 | h447
              · rcases m.htr 0 1 4 (by decide) (by decide) with h448 | h448
                · rcases m.htr 0 1 5 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h450 | h450
                    · linarith only [h450, hlam, p0_0]
                    · linarith only [h450, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h355, h449, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h454 | h454
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h455 | h455
                    · linarith only [h455, hlam, p0_0]
                    · linarith only [h422, h447, h455, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h355, h454, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h459 | h459
                · rcases m.htr 0 1 5 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h461 | h461
                    · linarith only [h461, hlam, p0_0]
                    · linarith only [h422, h447, h461, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · linarith only [h355, h460, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h465 | h465
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h466 | h466
                    · linarith only [h466, hlam, p0_0]
                    · linarith only [h422, h447, h465, h466, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                  · linarith only [h355, h465, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h470 | h470
            · rcases m.htr 0 1 2 (by decide) (by decide) with h471 | h471
              · rcases m.htr 0 1 4 (by decide) (by decide) with h472 | h472
                · rcases m.htr 0 1 5 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
                    · linarith only [h474, hlam, p0_0]
                    · linarith only [h470, h474, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h355, h473, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h478 | h478
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h479 | h479
                    · linarith only [h479, hlam, p0_0]
                    · linarith only [h470, h471, h479, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h355, h478, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h483 | h483
                · rcases m.htr 0 1 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
                    · linarith only [h485, hlam, p0_0]
                    · linarith only [h470, h471, h485, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h355, h484, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h490 | h490
                    · linarith only [h490, hlam, p0_0]
                    · linarith only [h470, h471, h489, h490, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                  · linarith only [h355, h489, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h494 | h494
              · rcases m.htr 0 1 4 (by decide) (by decide) with h495 | h495
                · rcases m.htr 0 1 5 (by decide) (by decide) with h496 | h496
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h497 | h497
                    · linarith only [h497, hlam, p0_0]
                    · linarith only [h494, h497, hc12, hc25, hlam, hphi, p0_1]
                  · linarith only [h355, h496, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h502 | h502
                    · linarith only [h502, hlam, p0_0]
                    · linarith only [h494, h502, hc12, hc25, hlam, hphi, p0_1]
                  · linarith only [h355, h501, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h506 | h506
                · rcases m.htr 0 1 5 (by decide) (by decide) with h507 | h507
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h508 | h508
                    · linarith only [h508, hlam, p0_0]
                    · linarith only [h494, h508, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · linarith only [h355, h507, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h513 | h513
                    · linarith only [h513, hlam, p0_0]
                    · linarith only [h494, h512, h513, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h355, h512, hlam]
        · linarith only [h421, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h518 | h518
    · linarith only [h518, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h520 | h520
      · linarith only [h520, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h522 | h522
        · rcases p0_3 (m.d 3 5) (by simp) with h523 | h523
          · rcases p0_3 (m.d 4 5) (by simp) with h524 | h524
            · rcases m.htr 0 1 2 (by decide) (by decide) with h525 | h525
              · rcases m.htr 0 1 4 (by decide) (by decide) with h526 | h526
                · rcases m.htr 0 1 5 (by decide) (by decide) with h527 | h527
                  · linarith only [h518, h527, hlam]
                  · linarith only [h525, h527, hc12, hc25, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
                  · linarith only [h518, h530, hlam]
                  · linarith only [h524, h525, h530, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h533 | h533
                · rcases m.htr 0 1 5 (by decide) (by decide) with h534 | h534
                  · linarith only [h518, h534, hlam]
                  · linarith only [h524, h534, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h537 | h537
                  · linarith only [h518, h537, hlam]
                  · linarith only [h524, h537, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h540 | h540
              · rcases m.htr 0 1 4 (by decide) (by decide) with h541 | h541
                · rcases m.htr 0 1 5 (by decide) (by decide) with h542 | h542
                  · linarith only [h518, h542, hlam]
                  · linarith only [h540, h542, hc12, hc25, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h545 | h545
                  · linarith only [h518, h545, hlam]
                  · linarith only [h523, h540, h545, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h548 | h548
                · rcases m.htr 0 1 5 (by decide) (by decide) with h549 | h549
                  · linarith only [h518, h549, hlam]
                  · linarith only [h523, h549, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h552 | h552
                  · linarith only [h518, h552, hlam]
                  · linarith only [h523, h552, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h555 | h555
            · rcases m.htr 0 1 2 (by decide) (by decide) with h556 | h556
              · rcases m.htr 0 1 4 (by decide) (by decide) with h557 | h557
                · rcases m.htr 0 1 5 (by decide) (by decide) with h558 | h558
                  · linarith only [h518, h558, hlam]
                  · linarith only [h555, h556, h558, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h561 | h561
                  · linarith only [h518, h561, hlam]
                  · linarith only [h555, h556, h561, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h564 | h564
                · rcases m.htr 0 1 5 (by decide) (by decide) with h565 | h565
                  · linarith only [h518, h565, hlam]
                  · linarith only [h555, h564, h565, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h568 | h568
                  · linarith only [h518, h568, hlam]
                  · linarith only [h555, h568, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h571 | h571
              · rcases m.htr 0 1 4 (by decide) (by decide) with h572 | h572
                · rcases m.htr 0 1 5 (by decide) (by decide) with h573 | h573
                  · linarith only [h518, h573, hlam]
                  · linarith only [h571, h573, hc12, hc25, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h576 | h576
                  · linarith only [h518, h576, hlam]
                  · linarith only [h571, h576, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h579 | h579
                · rcases m.htr 0 1 5 (by decide) (by decide) with h580 | h580
                  · linarith only [h518, h580, hlam]
                  · linarith only [h580, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h583 | h583
                  · linarith only [h518, h583, hlam]
                  · linarith only [h583, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h522, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h588 | h588
    · linarith only [h588, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h590 | h590
      · rcases p0_3 (m.d 2 5) (by simp) with h591 | h591
        · rcases p0_3 (m.d 3 5) (by simp) with h592 | h592
          · linarith only [h592, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h594 | h594
            · rcases m.htr 0 1 2 (by decide) (by decide) with h595 | h595
              · rcases m.htr 0 1 4 (by decide) (by decide) with h596 | h596
                · rcases m.htr 0 1 5 (by decide) (by decide) with h597 | h597
                  · linarith only [h590, h597, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h588, h597, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h600 | h600
                  · linarith only [h588, h590, h600, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h588, h600, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h603 | h603
                · rcases m.htr 0 1 5 (by decide) (by decide) with h604 | h604
                  · linarith only [h588, h590, h604, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h588, h604, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h607 | h607
                  · linarith only [h588, h590, h607, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h588, h607, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h610 | h610
              · rcases m.htr 0 1 4 (by decide) (by decide) with h611 | h611
                · rcases m.htr 0 1 5 (by decide) (by decide) with h612 | h612
                  · linarith only [h588, h590, h612, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h588, h612, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h615 | h615
                  · linarith only [h588, h590, h611, h615, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h588, h615, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h618 | h618
                · rcases m.htr 0 1 5 (by decide) (by decide) with h619 | h619
                  · linarith only [h588, h590, h610, h619, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h588, h619, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h622 | h622
                  · linarith only [h588, h590, h618, h622, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h588, h622, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h591, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h626 | h626
        · rcases p0_3 (m.d 3 5) (by simp) with h627 | h627
          · linarith only [h627, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h629 | h629
            · rcases m.htr 0 1 2 (by decide) (by decide) with h630 | h630
              · rcases m.htr 0 1 4 (by decide) (by decide) with h631 | h631
                · rcases m.htr 0 1 5 (by decide) (by decide) with h632 | h632
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h633 | h633
                    · linarith only [h588, h630, h633, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h588, h633, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h590, h629, h632, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h638 | h638
                    · linarith only [h588, h638, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h588, h629, h638, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h590, h629, h630, h637, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h642 | h642
                · rcases m.htr 0 1 5 (by decide) (by decide) with h643 | h643
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h644 | h644
                    · linarith only [h588, h643, h644, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h588, h629, h644, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h590, h629, h642, h643, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h648 | h648
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h649 | h649
                    · linarith only [h588, h648, h649, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h588, h629, h649, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h590, h629, h648, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h653 | h653
              · rcases m.htr 0 1 4 (by decide) (by decide) with h654 | h654
                · rcases m.htr 0 1 5 (by decide) (by decide) with h655 | h655
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h656 | h656
                    · linarith only [h588, h656, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h588, h656, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h590, h653, h655, hc12, hc25, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h661 | h661
                    · linarith only [h588, h661, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h588, h661, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h590, h653, h660, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h665 | h665
                · rcases m.htr 0 1 5 (by decide) (by decide) with h666 | h666
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h667 | h667
                    · linarith only [h588, h667, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h588, h667, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h590, h665, h666, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h671 | h671
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h672 | h672
                    · linarith only [h588, h672, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h588, h672, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h590, h671, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h626, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h677 | h677
    · linarith only [h677, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h679 | h679
      · rcases p0_3 (m.d 2 5) (by simp) with h680 | h680
        · rcases p0_3 (m.d 3 5) (by simp) with h681 | h681
          · rcases p0_3 (m.d 4 5) (by simp) with h682 | h682
            · linarith only [h682, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h684 | h684
              · rcases m.htr 0 1 4 (by decide) (by decide) with h685 | h685
                · rcases m.htr 0 1 5 (by decide) (by decide) with h686 | h686
                  · linarith only [h679, h686, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h677, h686, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h689 | h689
                  · linarith only [h677, h679, h689, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h677, h689, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h692 | h692
                · rcases m.htr 0 1 5 (by decide) (by decide) with h693 | h693
                  · linarith only [h677, h679, h693, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h677, h693, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h696 | h696
                  · linarith only [h677, h679, h692, h696, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h677, h696, hc01, hc25, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h699 | h699
            · linarith only [h699, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h701 | h701
              · rcases m.htr 0 1 4 (by decide) (by decide) with h702 | h702
                · rcases m.htr 0 1 5 (by decide) (by decide) with h703 | h703
                  · linarith only [h677, h679, h703, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h677, h703, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h706 | h706
                  · linarith only [h677, h679, h702, h706, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h677, h706, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h709 | h709
                · rcases m.htr 0 1 5 (by decide) (by decide) with h710 | h710
                  · linarith only [h677, h679, h701, h710, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h677, h710, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h713 | h713
                  · linarith only [h677, h679, h713, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h677, h713, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h680, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h717 | h717
        · rcases p0_3 (m.d 3 5) (by simp) with h718 | h718
          · rcases p0_3 (m.d 4 5) (by simp) with h719 | h719
            · linarith only [h719, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h721 | h721
              · rcases m.htr 0 1 4 (by decide) (by decide) with h722 | h722
                · rcases m.htr 0 1 5 (by decide) (by decide) with h723 | h723
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h724 | h724
                    · linarith only [h677, h721, h724, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h677, h718, h724, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h679, h718, h723, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h728 | h728
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h729 | h729
                    · linarith only [h677, h729, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h677, h729, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h679, h718, h721, h728, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h733 | h733
                · rcases m.htr 0 1 5 (by decide) (by decide) with h734 | h734
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h735 | h735
                    · linarith only [h677, h735, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h677, h718, h735, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h679, h718, h733, h734, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h739 | h739
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h740 | h740
                    · linarith only [h677, h740, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h677, h718, h740, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h679, h718, h739, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h744 | h744
            · linarith only [h744, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h746 | h746
              · rcases m.htr 0 1 4 (by decide) (by decide) with h747 | h747
                · rcases m.htr 0 1 5 (by decide) (by decide) with h748 | h748
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h749 | h749
                    · linarith only [h677, h749, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h677, h749, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h679, h746, h748, hc12, hc25, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h753 | h753
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h754 | h754
                    · linarith only [h677, h754, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h677, h754, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h679, h746, h753, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h758 | h758
                · rcases m.htr 0 1 5 (by decide) (by decide) with h759 | h759
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h760 | h760
                    · linarith only [h677, h760, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h677, h760, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h679, h758, h759, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h764 | h764
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h765 | h765
                    · linarith only [h677, h765, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h677, h765, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h679, h764, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h717, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h770 | h770
    · linarith only [h770, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h772 | h772
      · rcases p0_3 (m.d 2 5) (by simp) with h773 | h773
        · rcases p0_3 (m.d 3 5) (by simp) with h774 | h774
          · rcases p0_3 (m.d 4 5) (by simp) with h775 | h775
            · rcases m.htr 0 1 2 (by decide) (by decide) with h776 | h776
              · rcases m.htr 0 1 4 (by decide) (by decide) with h777 | h777
                · rcases m.htr 0 1 5 (by decide) (by decide) with h778 | h778
                  · linarith only [h772, h778, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h778, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h781 | h781
                  · linarith only [h772, h781, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h781, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h784 | h784
                · rcases m.htr 0 1 5 (by decide) (by decide) with h785 | h785
                  · linarith only [h772, h785, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h785, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h788 | h788
                  · linarith only [h772, h788, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h788, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h791 | h791
              · rcases m.htr 0 1 4 (by decide) (by decide) with h792 | h792
                · rcases m.htr 0 1 5 (by decide) (by decide) with h793 | h793
                  · linarith only [h772, h793, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h793, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h796 | h796
                  · linarith only [h772, h792, h796, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h796, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h799 | h799
                · rcases m.htr 0 1 5 (by decide) (by decide) with h800 | h800
                  · linarith only [h772, h800, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h800, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h803 | h803
                  · linarith only [h772, h803, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h803, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h774, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h807 | h807
          · rcases p0_3 (m.d 4 5) (by simp) with h808 | h808
            · rcases m.htr 0 1 2 (by decide) (by decide) with h809 | h809
              · rcases m.htr 0 1 4 (by decide) (by decide) with h810 | h810
                · rcases m.htr 0 1 5 (by decide) (by decide) with h811 | h811
                  · linarith only [h772, h811, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h811, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h814 | h814
                  · linarith only [h772, h810, h814, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h814, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h817 | h817
                · rcases m.htr 0 1 5 (by decide) (by decide) with h818 | h818
                  · linarith only [h772, h818, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h818, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h821 | h821
                  · linarith only [h772, h821, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h821, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h824 | h824
              · rcases m.htr 0 1 4 (by decide) (by decide) with h825 | h825
                · rcases m.htr 0 1 5 (by decide) (by decide) with h826 | h826
                  · linarith only [h772, h826, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h826, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h829 | h829
                  · linarith only [h772, h825, h829, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h829, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h832 | h832
                · rcases m.htr 0 1 5 (by decide) (by decide) with h833 | h833
                  · linarith only [h772, h824, h833, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h833, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h836 | h836
                  · linarith only [h772, h836, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h836, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h807, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h840 | h840
        · rcases p0_3 (m.d 3 5) (by simp) with h841 | h841
          · rcases p0_3 (m.d 4 5) (by simp) with h842 | h842
            · rcases m.htr 0 1 2 (by decide) (by decide) with h843 | h843
              · rcases m.htr 0 1 4 (by decide) (by decide) with h844 | h844
                · rcases m.htr 0 1 5 (by decide) (by decide) with h845 | h845
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h846 | h846
                    · linarith only [h840, h843, h846, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h846, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h772, h845, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h851 | h851
                    · linarith only [h840, h851, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h851, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h772, h850, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h855 | h855
                · rcases m.htr 0 1 5 (by decide) (by decide) with h856 | h856
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h857 | h857
                    · linarith only [h840, h857, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h857, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h772, h856, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h862 | h862
                    · linarith only [h840, h862, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h862, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h772, h861, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h866 | h866
              · rcases m.htr 0 1 4 (by decide) (by decide) with h867 | h867
                · rcases m.htr 0 1 5 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h869 | h869
                    · linarith only [h840, h869, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h840, h869, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h772, h868, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h873 | h873
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h874 | h874
                    · linarith only [h840, h874, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h840, h874, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h772, h873, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h878 | h878
                · rcases m.htr 0 1 5 (by decide) (by decide) with h879 | h879
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h880 | h880
                    · linarith only [h840, h880, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h880, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h772, h879, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h884 | h884
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h885 | h885
                    · linarith only [h840, h885, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h885, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h772, h884, hlam]
          · linarith only [h841, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h890 | h890
          · rcases p0_3 (m.d 4 5) (by simp) with h891 | h891
            · rcases m.htr 0 1 2 (by decide) (by decide) with h892 | h892
              · rcases m.htr 0 1 4 (by decide) (by decide) with h893 | h893
                · rcases m.htr 0 1 5 (by decide) (by decide) with h894 | h894
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h895 | h895
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h896 | h896
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h897 | h897
                        · linarith only [h897, hlam, p0_0]
                        · linarith only [h891, h897, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h900 | h900
                        · linarith only [h900, hlam, p0_0]
                        · linarith only [h891, h900, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h840, h895, hlam]
                  · linarith only [h772, h894, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h905 | h905
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h906 | h906
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h907 | h907
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h908 | h908
                        · linarith only [h908, hlam, p0_0]
                        · linarith only [h891, h908, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h911 | h911
                        · linarith only [h911, hlam, p0_0]
                        · linarith only [h891, h911, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h840, h906, hlam]
                  · linarith only [h772, h905, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h916 | h916
                · rcases m.htr 0 1 5 (by decide) (by decide) with h917 | h917
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h918 | h918
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h919 | h919
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h920 | h920
                        · linarith only [h920, hlam, p0_0]
                        · linarith only [h891, h920, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h923 | h923
                        · linarith only [h923, hlam, p0_0]
                        · linarith only [h891, h923, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h840, h918, hlam]
                  · linarith only [h772, h917, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h928 | h928
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h929 | h929
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h930 | h930
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h931 | h931
                        · linarith only [h931, hlam, p0_0]
                        · linarith only [h891, h916, h930, h931, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h934 | h934
                        · linarith only [h934, hlam, p0_0]
                        · linarith only [h934, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h840, h929, hlam]
                  · linarith only [h772, h928, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h939 | h939
              · rcases m.htr 0 1 4 (by decide) (by decide) with h940 | h940
                · rcases m.htr 0 1 5 (by decide) (by decide) with h941 | h941
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h942 | h942
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h943 | h943
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h944 | h944
                        · linarith only [h944, hlam, p0_0]
                        · linarith only [h944, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h947 | h947
                        · linarith only [h947, hlam, p0_0]
                        · linarith only [h947, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h840, h942, hlam]
                  · linarith only [h772, h941, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h952 | h952
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h953 | h953
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h954 | h954
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h955 | h955
                        · linarith only [h955, hlam, p0_0]
                        · linarith only [h939, h940, h954, h955, hc12, hc35, hlam, hphi, ht23, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h958 | h958
                        · linarith only [h958, hlam, p0_0]
                        · linarith only [h958, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h840, h953, hlam]
                  · linarith only [h772, h952, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h963 | h963
                · rcases m.htr 0 1 5 (by decide) (by decide) with h964 | h964
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h965 | h965
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h966 | h966
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h967 | h967
                        · linarith only [h967, hlam, p0_0]
                        · linarith only [h967, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h970 | h970
                        · linarith only [h970, hlam, p0_0]
                        · linarith only [h970, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h840, h965, hlam]
                  · linarith only [h772, h964, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h975 | h975
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h976 | h976
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h977 | h977
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h978 | h978
                        · linarith only [h978, hlam, p0_0]
                        · linarith only [h978, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h981 | h981
                        · linarith only [h981, hlam, p0_0]
                        · linarith only [h981, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h840, h976, hlam]
                  · linarith only [h772, h975, hlam]
          · linarith only [h890, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h987 | h987
    · linarith only [h987, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h989 | h989
      · linarith only [h989, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h991 | h991
        · rcases p0_3 (m.d 3 5) (by simp) with h992 | h992
          · rcases p0_3 (m.d 4 5) (by simp) with h993 | h993
            · rcases m.htr 0 1 2 (by decide) (by decide) with h994 | h994
              · rcases m.htr 0 1 4 (by decide) (by decide) with h995 | h995
                · rcases m.htr 0 1 5 (by decide) (by decide) with h996 | h996
                  · linarith only [h987, h996, hlam]
                  · linarith only [h991, h996, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h999 | h999
                  · linarith only [h987, h999, hlam]
                  · linarith only [h993, h994, h999, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1002 | h1002
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1003 | h1003
                  · linarith only [h1003, h987, hlam]
                  · linarith only [h1003, h993, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1006 | h1006
                  · linarith only [h1006, h987, hlam]
                  · linarith only [h1006, h993, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1009 | h1009
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1011 | h1011
                  · linarith only [h1011, h987, hlam]
                  · linarith only [h1009, h1011, hc12, hc35, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1014 | h1014
                  · linarith only [h1014, h987, hlam]
                  · linarith only [h1009, h1014, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1017 | h1017
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1018 | h1018
                  · linarith only [h1018, h987, hlam]
                  · linarith only [h1018, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1021 | h1021
                  · linarith only [h1021, h987, hlam]
                  · linarith only [h1021, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h992, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1025 | h1025
          · rcases p0_3 (m.d 4 5) (by simp) with h1026 | h1026
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1027 | h1027
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1028 | h1028
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1029 | h1029
                  · linarith only [h1029, h987, hlam]
                  · linarith only [h1026, h1029, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1032 | h1032
                  · linarith only [h1032, h987, hlam]
                  · linarith only [h1026, h1027, h1032, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1035 | h1035
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1036 | h1036
                  · linarith only [h1036, h987, hlam]
                  · linarith only [h1026, h1035, h1036, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1039 | h1039
                  · linarith only [h1039, h987, hlam]
                  · linarith only [h1026, h1039, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1042 | h1042
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1043 | h1043
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1044 | h1044
                  · linarith only [h1044, h987, hlam]
                  · linarith only [h1042, h1044, hc12, hc35, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1047 | h1047
                  · linarith only [h1047, h987, hlam]
                  · linarith only [h1042, h1047, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1050 | h1050
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1051 | h1051
                  · linarith only [h1051, h987, hlam]
                  · linarith only [h1050, h1051, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1054 | h1054
                  · linarith only [h1054, h987, hlam]
                  · linarith only [h1054, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1025, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1058 | h1058
    · linarith only [h1058, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1060 | h1060
      · rcases p0_3 (m.d 2 5) (by simp) with h1061 | h1061
        · linarith only [h1061, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1063 | h1063
          · rcases p0_3 (m.d 4 5) (by simp) with h1064 | h1064
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1065 | h1065
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1066 | h1066
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1067 | h1067
                  · linarith only [h1060, h1067, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1058, h1067, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1070 | h1070
                  · linarith only [h1058, h1060, h1070, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1058, h1070, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1073 | h1073
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1074 | h1074
                  · linarith only [h1058, h1060, h1074, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1058, h1074, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1077 | h1077
                  · linarith only [h1058, h1060, h1073, h1077, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1058, h1077, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1080 | h1080
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1081 | h1081
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1082 | h1082
                  · linarith only [h1058, h1060, h1082, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1058, h1082, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1085 | h1085
                  · linarith only [h1058, h1060, h1081, h1085, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1058, h1085, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1089 | h1089
                  · linarith only [h1058, h1060, h1080, h1089, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h1058, h1089, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1092 | h1092
                  · linarith only [h1058, h1060, h1092, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1058, h1092, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1063, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1096 | h1096
        · linarith only [h1096, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1098 | h1098
          · rcases p0_3 (m.d 4 5) (by simp) with h1099 | h1099
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1100 | h1100
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1101 | h1101
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1102 | h1102
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1103 | h1103
                    · linarith only [h1058, h1103, hlam]
                    · linarith only [h1099, h1103, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1060, h1099, h1102, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1107 | h1107
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1108 | h1108
                    · linarith only [h1058, h1108, hlam]
                    · linarith only [h1099, h1108, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1060, h1099, h1100, h1107, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1112 | h1112
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1113 | h1113
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1114 | h1114
                    · linarith only [h1058, h1114, hlam]
                    · linarith only [h1099, h1100, h1112, h1114, hc14, hc45, hlam, hphi, p0_1]
                  · linarith only [h1060, h1099, h1112, h1113, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1118 | h1118
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1119 | h1119
                    · linarith only [h1058, h1119, hlam]
                    · linarith only [h1099, h1100, h1119, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1060, h1099, h1118, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1123 | h1123
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1124 | h1124
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1125 | h1125
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1126 | h1126
                    · linarith only [h1058, h1126, hlam]
                    · linarith only [h1126, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1060, h1123, h1125, hc12, hc35, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1130 | h1130
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1131 | h1131
                    · linarith only [h1058, h1131, hlam]
                    · linarith only [h1123, h1131, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1060, h1123, h1130, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1135 | h1135
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1136 | h1136
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1137 | h1137
                    · linarith only [h1058, h1137, hlam]
                    · linarith only [h1123, h1135, h1137, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · linarith only [h1060, h1135, h1136, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1141 | h1141
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1142 | h1142
                    · linarith only [h1058, h1142, hlam]
                    · linarith only [h1123, h1142, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · linarith only [h1060, h1141, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1098, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1148 | h1148
    · linarith only [h1148, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1150 | h1150
      · rcases p0_3 (m.d 2 5) (by simp) with h1151 | h1151
        · rcases p0_3 (m.d 3 5) (by simp) with h1152 | h1152
          · rcases p0_3 (m.d 4 5) (by simp) with h1153 | h1153
            · linarith only [h1153, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1155 | h1155
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1156 | h1156
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1157 | h1157
                  · linarith only [h1150, h1157, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1148, h1151, h1157, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1160 | h1160
                  · linarith only [h1148, h1150, h1160, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1148, h1160, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1163 | h1163
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1164 | h1164
                  · linarith only [h1148, h1150, h1164, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1148, h1164, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1167 | h1167
                  · linarith only [h1148, h1150, h1167, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1148, h1150, h1167, hc01, hc15, hlam, hphi, p0_1]
          · linarith only [h1152, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1171 | h1171
          · rcases p0_3 (m.d 4 5) (by simp) with h1172 | h1172
            · linarith only [h1172, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1174 | h1174
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1175 | h1175
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1176 | h1176
                  · linarith only [h1148, h1150, h1176, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1148, h1176, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1179 | h1179
                  · linarith only [h1148, h1150, h1175, h1179, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1148, h1179, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1182 | h1182
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1183 | h1183
                  · linarith only [h1148, h1150, h1174, h1183, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h1148, h1183, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1186 | h1186
                  · linarith only [h1148, h1150, h1186, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1148, h1186, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1171, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1190 | h1190
        · rcases p0_3 (m.d 3 5) (by simp) with h1191 | h1191
          · rcases p0_3 (m.d 4 5) (by simp) with h1192 | h1192
            · linarith only [h1192, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1194 | h1194
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1195 | h1195
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1196 | h1196
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1197 | h1197
                    · linarith only [h1148, h1190, h1194, h1197, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h1148, h1197, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1150, h1196, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1201 | h1201
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1202 | h1202
                    · linarith only [h1148, h1190, h1202, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1148, h1190, h1202, hc02, hc25, hlam, hphi, p0_1]
                  · linarith only [h1150, h1194, h1201, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1206 | h1206
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1207 | h1207
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1208 | h1208
                    · linarith only [h1148, h1190, h1208, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1148, h1208, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1150, h1207, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1212 | h1212
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1213 | h1213
                    · linarith only [h1148, h1190, h1213, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1148, h1213, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1150, h1212, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1191, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1218 | h1218
          · rcases p0_3 (m.d 4 5) (by simp) with h1219 | h1219
            · linarith only [h1219, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1221 | h1221
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1222 | h1222
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1223 | h1223
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1224 | h1224
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1225 | h1225
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1226 | h1226
                        · linarith only [h1148, h1226, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1148, h1226, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1229 | h1229
                        · linarith only [h1148, h1225, h1229, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                        · linarith only [h1148, h1229, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h1190, h1224, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1150, h1221, h1223, hc12, hc35, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1234 | h1234
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1237 | h1237
                        · linarith only [h1148, h1237, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1148, h1237, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1240 | h1240
                        · linarith only [h1148, h1240, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1148, h1240, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h1190, h1235, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1150, h1221, h1234, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1245 | h1245
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1246 | h1246
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1247 | h1247
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1248 | h1248
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1249 | h1249
                        · linarith only [h1148, h1249, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1148, h1249, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1252 | h1252
                        · linarith only [h1148, h1252, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1148, h1252, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h1190, h1221, h1245, h1247, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                  · linarith only [h1150, h1245, h1246, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1257 | h1257
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1258 | h1258
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1259 | h1259
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1260 | h1260
                        · linarith only [h1148, h1260, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1148, h1260, hc03, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1263 | h1263
                        · linarith only [h1148, h1263, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1148, h1263, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h1190, h1221, h1258, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · linarith only [h1150, h1257, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1218, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1269 | h1269
    · linarith only [h1269, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h1271 | h1271
      · rcases p0_3 (m.d 2 5) (by simp) with h1272 | h1272
        · rcases p0_3 (m.d 3 5) (by simp) with h1273 | h1273
          · rcases p0_3 (m.d 4 5) (by simp) with h1274 | h1274
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1275 | h1275
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1276 | h1276
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1277 | h1277
                  · linarith only [h1271, h1277, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1272, h1277, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1280 | h1280
                  · linarith only [h1271, h1280, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1280, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1283 | h1283
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1284 | h1284
                  · linarith only [h1271, h1284, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1284, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1287 | h1287
                  · linarith only [h1271, h1287, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1287, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1274, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1291 | h1291
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1292 | h1292
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1293 | h1293
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1294 | h1294
                  · linarith only [h1271, h1294, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1294, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1297 | h1297
                  · linarith only [h1271, h1297, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1297, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1300 | h1300
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1301 | h1301
                  · linarith only [h1271, h1301, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1301, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1304 | h1304
                  · linarith only [h1271, h1300, h1304, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1304, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1291, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1308 | h1308
          · rcases p0_3 (m.d 4 5) (by simp) with h1309 | h1309
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1310 | h1310
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1311 | h1311
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1312 | h1312
                  · linarith only [h1271, h1312, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1308, h1312, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1315 | h1315
                  · linarith only [h1271, h1315, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1315, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1318 | h1318
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1319 | h1319
                  · linarith only [h1271, h1319, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1319, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1322 | h1322
                  · linarith only [h1271, h1318, h1322, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1322, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1309, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1326 | h1326
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1327 | h1327
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1328 | h1328
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1329 | h1329
                  · linarith only [h1271, h1329, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1329, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1332 | h1332
                  · linarith only [h1271, h1332, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1332, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1335 | h1335
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1336 | h1336
                  · linarith only [h1271, h1327, h1336, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h1336, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1339 | h1339
                  · linarith only [h1271, h1339, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1339, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1326, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1343 | h1343
        · rcases p0_3 (m.d 3 5) (by simp) with h1344 | h1344
          · rcases p0_3 (m.d 4 5) (by simp) with h1345 | h1345
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1346 | h1346
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1347 | h1347
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1348 | h1348
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1349 | h1349
                    · linarith only [h1343, h1346, h1348, h1349, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h1344, h1349, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · linarith only [h1271, h1348, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1353 | h1353
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1354 | h1354
                    · linarith only [h1343, h1354, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1354, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1271, h1353, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1358 | h1358
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1359 | h1359
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1360 | h1360
                    · linarith only [h1343, h1360, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1346, h1360, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1271, h1359, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1364 | h1364
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1365 | h1365
                    · linarith only [h1343, h1365, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1365, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1271, h1364, hlam]
            · linarith only [h1345, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1370 | h1370
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1371 | h1371
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1372 | h1372
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1373 | h1373
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1374 | h1374
                    · linarith only [h1343, h1373, h1374, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1374, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1271, h1373, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1378 | h1378
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1379 | h1379
                    · linarith only [h1343, h1378, h1379, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1379, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1271, h1378, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1383 | h1383
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1384 | h1384
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1385 | h1385
                    · linarith only [h1343, h1384, h1385, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1385, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1271, h1384, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1389 | h1389
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1390 | h1390
                    · linarith only [h1343, h1389, h1390, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1390, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1271, h1389, hlam]
            · linarith only [h1370, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1395 | h1395
          · rcases p0_3 (m.d 4 5) (by simp) with h1396 | h1396
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1397 | h1397
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1398 | h1398
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1399 | h1399
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1400 | h1400
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1401 | h1401
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1402 | h1402
                        · linarith only [h1395, h1399, h1402, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1402, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1405 | h1405
                        · linarith only [h1395, h1399, h1405, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1405, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1343, h1400, hlam]
                  · linarith only [h1271, h1399, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1410 | h1410
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1411 | h1411
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1412 | h1412
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1413 | h1413
                        · linarith only [h1395, h1410, h1413, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1398, h1412, h1413, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1416 | h1416
                        · linarith only [h1395, h1410, h1416, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1416, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1343, h1411, hlam]
                  · linarith only [h1271, h1410, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1421 | h1421
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1422 | h1422
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1423 | h1423
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1424 | h1424
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1425 | h1425
                        · linarith only [h1395, h1422, h1425, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1425, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1428 | h1428
                        · linarith only [h1395, h1422, h1428, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1428, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1343, h1423, hlam]
                  · linarith only [h1271, h1422, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1433 | h1433
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1434 | h1434
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1435 | h1435
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1436 | h1436
                        · linarith only [h1395, h1433, h1436, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1436, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1439 | h1439
                        · linarith only [h1395, h1433, h1439, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h1439, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1343, h1434, hlam]
                  · linarith only [h1271, h1433, hlam]
            · linarith only [h1396, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1445 | h1445
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1446 | h1446
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1447 | h1447
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1448 | h1448
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1449 | h1449
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1450 | h1450
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1451 | h1451
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1452 | h1452
                          · linarith only [h1452, hlam, p0_0]
                          · linarith only [h1447, h1452, hc14, hc45, hlam, hphi, p0_1]
                        · linarith only [h1395, h1451, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1456 | h1456
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1457 | h1457
                          · linarith only [h1457, hlam, p0_0]
                          · linarith only [h1450, h1456, h1457, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                        · linarith only [h1395, h1456, hlam]
                    · linarith only [h1343, h1449, hlam]
                  · linarith only [h1271, h1448, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1463 | h1463
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1464 | h1464
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1465 | h1465
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1466 | h1466
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1467 | h1467
                          · linarith only [h1467, hlam, p0_0]
                          · linarith only [h1446, h1447, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                        · linarith only [h1395, h1466, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1471 | h1471
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1472 | h1472
                          · linarith only [h1472, hlam, p0_0]
                          · linarith only [h1465, h1472, hc03, hc45, hlam, hphi, ht34, p0_1]
                        · linarith only [h1395, h1471, hlam]
                    · linarith only [h1343, h1464, hlam]
                  · linarith only [h1271, h1463, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1478 | h1478
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1479 | h1479
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1480 | h1480
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1481 | h1481
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1482 | h1482
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1483 | h1483
                          · linarith only [h1483, hlam, p0_0]
                          · linarith only [h1478, h1483, hc14, hc45, hlam, hphi, p0_1]
                        · linarith only [h1395, h1482, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1487 | h1487
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1488 | h1488
                          · linarith only [h1488, hlam, p0_0]
                          · linarith only [h1481, h1488, hc03, hc45, hlam, hphi, ht34, p0_1]
                        · linarith only [h1395, h1487, hlam]
                    · linarith only [h1343, h1480, hlam]
                  · linarith only [h1271, h1479, hlam]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1494 | h1494
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1495 | h1495
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1496 | h1496
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1497 | h1497
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1498 | h1498
                          · linarith only [h1498, hlam, p0_0]
                          · linarith only [h1478, h1498, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                        · linarith only [h1395, h1497, hlam]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1502 | h1502
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h1503 | h1503
                          · linarith only [h1503, hlam, p0_0]
                          · linarith only [h1478, h1494, h1503, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                        · linarith only [h1395, h1502, hlam]
                    · linarith only [h1343, h1495, hlam]
                  · linarith only [h1271, h1494, hlam]
            · linarith only [h1445, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1510 | h1510
    · linarith only [h1510, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1512 | h1512
      · linarith only [h1512, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1514 | h1514
        · rcases p0_3 (m.d 3 5) (by simp) with h1515 | h1515
          · rcases p0_3 (m.d 4 5) (by simp) with h1516 | h1516
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1517 | h1517
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1518 | h1518
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1519 | h1519
                  · linarith only [h1510, h1519, hlam]
                  · linarith only [h1514, h1519, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1522 | h1522
                  · linarith only [h1510, h1522, hlam]
                  · linarith only [h1517, h1522, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1525 | h1525
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1526 | h1526
                  · linarith only [h1510, h1526, hlam]
                  · linarith only [h1525, h1526, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1529 | h1529
                  · linarith only [h1510, h1529, hlam]
                  · linarith only [h1529, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1516, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1533 | h1533
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1534 | h1534
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1535 | h1535
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1536 | h1536
                  · linarith only [h1510, h1536, hlam]
                  · linarith only [h1534, h1536, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1539 | h1539
                  · linarith only [h1510, h1539, hlam]
                  · linarith only [h1534, h1539, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1542 | h1542
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1543 | h1543
                  · linarith only [h1510, h1543, hlam]
                  · linarith only [h1543, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1546 | h1546
                  · linarith only [h1510, h1546, hlam]
                  · linarith only [h1546, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1533, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1550 | h1550
          · rcases p0_3 (m.d 4 5) (by simp) with h1551 | h1551
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1552 | h1552
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1553 | h1553
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1554 | h1554
                  · linarith only [h1510, h1554, hlam]
                  · linarith only [h1552, h1554, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1557 | h1557
                  · linarith only [h1510, h1557, hlam]
                  · linarith only [h1552, h1557, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1560 | h1560
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1561 | h1561
                  · linarith only [h1510, h1561, hlam]
                  · linarith only [h1561, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1564 | h1564
                  · linarith only [h1510, h1564, hlam]
                  · linarith only [h1564, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1551, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1568 | h1568
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1569 | h1569
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1570 | h1570
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1571 | h1571
                  · linarith only [h1510, h1571, hlam]
                  · linarith only [h1571, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1574 | h1574
                  · linarith only [h1510, h1574, hlam]
                  · linarith only [h1569, h1574, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1577 | h1577
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1578 | h1578
                  · linarith only [h1510, h1578, hlam]
                  · linarith only [h1578, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1581 | h1581
                  · linarith only [h1510, h1581, hlam]
                  · linarith only [h1581, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1568, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1585 | h1585
    · linarith only [h1585, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1587 | h1587
      · rcases p0_3 (m.d 2 5) (by simp) with h1588 | h1588
        · linarith only [h1588, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1590 | h1590
          · rcases p0_3 (m.d 4 5) (by simp) with h1591 | h1591
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1592 | h1592
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1593 | h1593
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1594 | h1594
                  · linarith only [h1587, h1594, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1585, h1590, h1594, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1597 | h1597
                  · linarith only [h1585, h1587, h1593, h1597, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1585, h1597, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1600 | h1600
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1601 | h1601
                  · linarith only [h1585, h1587, h1592, h1601, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h1585, h1601, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1604 | h1604
                  · linarith only [h1585, h1587, h1604, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1585, h1604, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1591, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1608 | h1608
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1609 | h1609
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1610 | h1610
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1611 | h1611
                  · linarith only [h1585, h1587, h1611, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1585, h1611, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1614 | h1614
                  · linarith only [h1585, h1587, h1610, h1614, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1585, h1614, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1617 | h1617
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1618 | h1618
                  · linarith only [h1585, h1587, h1609, h1618, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h1585, h1618, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1621 | h1621
                  · linarith only [h1585, h1587, h1621, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1585, h1621, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1608, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1625 | h1625
        · linarith only [h1625, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1627 | h1627
          · rcases p0_3 (m.d 4 5) (by simp) with h1628 | h1628
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1629 | h1629
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1630 | h1630
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1631 | h1631
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1632 | h1632
                    · linarith only [h1585, h1632, hlam]
                    · linarith only [h1632, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1587, h1629, h1631, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1636 | h1636
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1637 | h1637
                    · linarith only [h1585, h1637, hlam]
                    · linarith only [h1629, h1637, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1587, h1629, h1636, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1641 | h1641
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1642 | h1642
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1643 | h1643
                    · linarith only [h1585, h1643, hlam]
                    · linarith only [h1629, h1641, h1643, hc14, hc45, hlam, hphi, p0_1]
                  · linarith only [h1587, h1641, h1642, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1647 | h1647
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1648 | h1648
                    · linarith only [h1585, h1648, hlam]
                    · linarith only [h1629, h1648, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1587, h1647, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1628, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1653 | h1653
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1654 | h1654
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1655 | h1655
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1656 | h1656
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1657 | h1657
                    · linarith only [h1585, h1657, hlam]
                    · linarith only [h1657, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1587, h1654, h1656, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1661 | h1661
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1662 | h1662
                    · linarith only [h1585, h1662, hlam]
                    · linarith only [h1654, h1662, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1587, h1654, h1661, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1666 | h1666
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1667 | h1667
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1668 | h1668
                    · linarith only [h1585, h1668, hlam]
                    · linarith only [h1654, h1668, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1587, h1666, h1667, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1672 | h1672
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1673 | h1673
                    · linarith only [h1585, h1673, hlam]
                    · linarith only [h1654, h1673, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · linarith only [h1587, h1672, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1653, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1678 | h1678
    · linarith only [h1678, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1680 | h1680
      · rcases p0_3 (m.d 2 5) (by simp) with h1681 | h1681
        · rcases p0_3 (m.d 3 5) (by simp) with h1682 | h1682
          · linarith only [h1682, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1684 | h1684
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1685 | h1685
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1686 | h1686
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1687 | h1687
                  · linarith only [h1680, h1687, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1678, h1681, h1687, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1690 | h1690
                  · linarith only [h1678, h1680, h1690, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1678, h1681, h1690, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1693 | h1693
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1694 | h1694
                  · linarith only [h1678, h1680, h1694, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1678, h1694, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1697 | h1697
                  · linarith only [h1678, h1680, h1697, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1678, h1697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1684, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1701 | h1701
          · linarith only [h1701, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1703 | h1703
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1704 | h1704
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1705 | h1705
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1706 | h1706
                  · linarith only [h1678, h1680, h1706, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h1678, h1706, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1709 | h1709
                  · linarith only [h1678, h1680, h1705, h1709, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
                  · linarith only [h1678, h1709, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1712 | h1712
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1713 | h1713
                  · linarith only [h1678, h1680, h1704, h1713, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h1678, h1713, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1716 | h1716
                  · linarith only [h1678, h1680, h1704, h1716, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h1678, h1716, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1703, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1720 | h1720
        · rcases p0_3 (m.d 3 5) (by simp) with h1721 | h1721
          · linarith only [h1721, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1723 | h1723
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1724 | h1724
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1725 | h1725
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1726 | h1726
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1727 | h1727
                    · linarith only [h1678, h1720, h1727, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1678, h1727, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1680, h1724, h1726, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1731 | h1731
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1732 | h1732
                    · linarith only [h1678, h1720, h1731, h1732, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1678, h1732, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1680, h1724, h1731, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1736 | h1736
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1737 | h1737
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1738 | h1738
                    · linarith only [h1678, h1720, h1737, h1738, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1678, h1738, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1680, h1736, h1737, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1742 | h1742
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1743 | h1743
                    · linarith only [h1678, h1720, h1742, h1743, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1678, h1743, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1680, h1742, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1723, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1748 | h1748
          · linarith only [h1748, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1750 | h1750
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1751 | h1751
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1752 | h1752
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1753 | h1753
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1754 | h1754
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1755 | h1755
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1756 | h1756
                        · linarith only [h1678, h1756, hlam]
                        · linarith only [h1755, h1756, hc34, hc45, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1759 | h1759
                        · linarith only [h1678, h1759, hlam]
                        · linarith only [h1759, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1720, h1754, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1680, h1751, h1753, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1764 | h1764
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1765 | h1765
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1766 | h1766
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1767 | h1767
                        · linarith only [h1678, h1767, hlam]
                        · linarith only [h1751, h1752, h1766, h1767, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1770 | h1770
                        · linarith only [h1678, h1770, hlam]
                        · linarith only [h1770, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1720, h1765, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · linarith only [h1680, h1751, h1764, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h1775 | h1775
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1776 | h1776
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1777 | h1777
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1778 | h1778
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1779 | h1779
                        · linarith only [h1678, h1779, hlam]
                        · linarith only [h1778, h1779, hc34, hc45, hlam, hphi, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1782 | h1782
                        · linarith only [h1678, h1782, hlam]
                        · linarith only [h1782, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1720, h1751, h1775, h1777, hc14, hc45, hlam, hphi, p0_1]
                  · linarith only [h1680, h1775, h1776, hc14, hc45, hlam, hphi, p0_1]
                · rcases m.htr 0 1 5 (by decide) (by decide) with h1787 | h1787
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1788 | h1788
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h1789 | h1789
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1790 | h1790
                        · linarith only [h1678, h1790, hlam]
                        · linarith only [h1775, h1789, h1790, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                      · rcases m.htr 0 3 5 (by decide) (by decide) with h1793 | h1793
                        · linarith only [h1678, h1793, hlam]
                        · linarith only [h1793, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1720, h1751, h1787, h1788, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                  · linarith only [h1680, h1787, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1750, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

set_option maxHeartbeats 4360000 in
theorem n7l_sBT1_M_LI_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5bigk := hb5.2.2.2
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
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h13 | h13
      · linarith only [h13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi0]
      · rcases p0_3 (m.d 2 5) (by simp) with h15 | h15
        · rcases p0_3 (m.d 3 5) (by simp) with h16 | h16
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · rcases m.htr 0 1 2 (by decide) (by decide) with h18 | h18
              · rcases m.htr 0 1 3 (by decide) (by decide) with h19 | h19
                · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h21 | h21
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h22 | h22
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h23 | h23
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h24, hlam, p0_0]
                          · linarith only [h17, h22, h24, hc23, hc45, hlam, hphi, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h27 | h27
                          · linarith only [h27, hlam, p0_0]
                          · linarith only [h17, h22, h27, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
                          · linarith only [h31, hlam, p0_0]
                          · linarith only [h17, h30, h31, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h34, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h36 | h36
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h37 | h37
                              · linarith only [h16, h37, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi0]
                              · linarith only [h17, h36, h37, hc34, hc45, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
                              · linarith only [h16, h36, h40, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h17, h20, h21, h42, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0, u5ehi1]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                                  · linarith only [h18, h22, h44, hlam]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                                    · linarith only [h18, h30, h46, hlam]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                                      · linarith only [h18, h21, h48, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                                        · linarith only [h16, h19, h36, h42, h50, hlam, p0_1]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                                          · linarith only [h17, h20, h42, h52, hlam, p0_1]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                                              · linarith only [h16, h55, hlam]
                                              · linarith only [h22, h36, h54, h55, hc02, hc35, hlam, hphi, ht23]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                                              · linarith only [h16, h58, hlam]
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                                                · linarith only [h17, h60, hlam]
                                                · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                                                  · linarith only [h21, h60, h62, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi1]
                                                  · linarith only [h22, h54, h62, hc02, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h13, h21, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h66 | h66
                    · linarith only [h20, h66, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h13, h66, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h19, h70, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h70, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h73 | h73
                    · linarith only [h19, h73, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h73, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h18, h78, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h78, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h81 | h81
                    · linarith only [h18, h81, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h81, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h18, h85, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h85, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h88 | h88
                    · linarith only [h18, h88, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h88, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h91 | h91
              · rcases m.htr 0 1 3 (by decide) (by decide) with h92 | h92
                · rcases m.htr 0 1 4 (by decide) (by decide) with h93 | h93
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h95 | h95
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h97 | h97
                          · linarith only [h97, hlam, p0_0]
                          · linarith only [h16, h95, h97, hc23, hc35, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
                          · linarith only [h100, hlam, p0_0]
                          · linarith only [h100, h16, h95, hc23, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h103 | h103
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h104 | h104
                          · linarith only [h104, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
                              · linarith only [h103, h104, h107, h16, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
                                · linarith only [h103, h107, h109, h16, h95, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                · linarith only [h109, h17, hlam]
                            · linarith only [h103, h106, h95, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h113 | h113
                          · linarith only [h113, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h115 | h115
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
                              · linarith only [h116, h16, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
                                · linarith only [h115, h116, h118, h16, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                · linarith only [h118, h17, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h121 | h121
                              · linarith only [h115, h121, h16, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                                  · linarith only [h124, h91, h95, hlam]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                                    · linarith only [h103, h123, h126, h91, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                                      · linarith only [h121, h128, h91, h95, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
                                        · linarith only [h121, h130, h16, h92, hlam, p0_1]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                                          · linarith only [h132, h93, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                          · linarith only [h123, h126, h132, h16, hc12, hc35, hlam, hphi, ht23, p0_1]
                                · linarith only [h123, h17, hlam]
                    · linarith only [h13, h94, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h137 | h137
                    · linarith only [h137, h93, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h13, h137, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h141 | h141
                    · linarith only [h141, h92, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h141, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h144 | h144
                    · linarith only [h144, h92, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h144, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h147 | h147
                · rcases m.htr 0 1 4 (by decide) (by decide) with h148 | h148
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h149 | h149
                    · linarith only [h149, h91, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h149, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
                    · linarith only [h152, h91, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h152, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h156 | h156
                    · linarith only [h156, h91, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h156, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h159 | h159
                    · linarith only [h159, h91, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h159, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h162 | h162
            · rcases m.htr 0 1 2 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 1 3 (by decide) (by decide) with h164 | h164
                · rcases m.htr 0 1 4 (by decide) (by decide) with h165 | h165
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h166 | h166
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h167 | h167
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h168 | h168
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h169 | h169
                          · linarith only [h169, hlam, p0_0]
                          · linarith only [h162, h167, h169, hc23, hc45, hlam, hphi, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h172 | h172
                          · linarith only [h172, hlam, p0_0]
                          · linarith only [h162, h167, h172, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h175 | h175
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
                          · linarith only [h176, hlam, p0_0]
                          · linarith only [h162, h175, h176, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h179 | h179
                          · linarith only [h179, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h181 | h181
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h182 | h182
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h183 | h183
                                · linarith only [h162, h166, h183, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi1]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
                                  · linarith only [h162, h163, h167, h175, h182, h183, h185, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi3]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h187 | h187
                                    · linarith only [h164, h175, h185, h187, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                                      · linarith only [h163, h166, h189, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
                                        · linarith only [h164, h191, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                                        · linarith only [h162, h182, h191, hc13, hc45, hlam, hphi, ht34, p0_1]
                              · linarith only [h16, h182, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h195 | h195
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h196 | h196
                                · linarith only [h162, h166, h196, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi1]
                                · linarith only [h162, h181, h195, h196, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi3]
                              · linarith only [h16, h195, hlam]
                    · linarith only [h13, h166, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h165, h201, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h13, h201, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h204 | h204
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h205 | h205
                    · linarith only [h164, h205, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h205, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h208 | h208
                    · linarith only [h164, h208, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h208, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h211 | h211
                · rcases m.htr 0 1 4 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h213 | h213
                    · linarith only [h163, h213, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h213, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
                    · linarith only [h163, h216, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h216, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h219 | h219
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
                    · linarith only [h163, h220, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h220, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h223 | h223
                    · linarith only [h163, h223, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h223, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
                · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h232, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
                              · linarith only [h230, h232, h235, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi3]
                              · linarith only [h16, h235, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
                              · linarith only [h231, h232, h234, h238, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi3]
                              · linarith only [h16, h238, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h241, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
                            · linarith only [h230, h231, h243, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h245 | h245
                              · linarith only [h230, h241, h245, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi3]
                              · linarith only [h16, h245, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
                          · linarith only [h249, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h251 | h251
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h252 | h252
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
                                · linarith only [h248, h249, h253, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                                · linarith only [h162, h253, hlam]
                              · linarith only [h16, h252, hlam]
                            · linarith only [h230, h248, h251, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h258 | h258
                          · linarith only [h258, hlam, p0_0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
                                  · linarith only [h226, h230, h263, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h265 | h265
                                    · linarith only [h226, h248, h262, h265, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                                      · linarith only [h226, h258, h267, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h269 | h269
                                        · linarith only [h227, h269, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                                        · linarith only [h261, h263, h269, hc12, hc25, hlam, hphi, p0_1]
                                · linarith only [h162, h262, hlam]
                              · linarith only [h16, h261, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h274 | h274
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                                  · linarith only [h226, h230, h276, hlam]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
                                    · linarith only [h227, h248, h260, h276, h278, hlam]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                                      · linarith only [h226, h258, h280, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h282 | h282
                                        · linarith only [h227, h282, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                                        · linarith only [h260, h274, h282, hc13, hc34, hlam, hphi]
                                · linarith only [h162, h275, hlam]
                              · linarith only [h16, h274, hlam]
                    · linarith only [h13, h229, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h228, h288, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h13, h288, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h292 | h292
                    · linarith only [h227, h292, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h292, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h295 | h295
                    · linarith only [h227, h295, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h13, h295, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h298 | h298
                · rcases m.htr 0 1 4 (by decide) (by decide) with h299 | h299
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h300 | h300
                    · linarith only [h226, h300, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h300, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h303 | h303
                    · linarith only [h226, h303, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h303, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h307 | h307
                    · linarith only [h226, h307, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h307, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h310 | h310
                    · linarith only [h226, h310, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h13, h310, hlam]
        · linarith only [h15, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h314 | h314
    · linarith only [h314, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · rcases p0_3 (m.d 1 5) (by simp) with h316 | h316
      · linarith only [h316, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h318 | h318
        · rcases p0_3 (m.d 3 5) (by simp) with h319 | h319
          · rcases p0_3 (m.d 4 5) (by simp) with h320 | h320
            · rcases m.htr 0 1 2 (by decide) (by decide) with h321 | h321
              · rcases m.htr 0 1 3 (by decide) (by decide) with h322 | h322
                · rcases m.htr 0 1 4 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h324 | h324
                    · linarith only [h314, h324, hlam]
                    · linarith only [h320, h324, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h327 | h327
                    · linarith only [h314, h327, hlam]
                    · linarith only [h320, h321, h327, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h314, h331, hlam]
                    · linarith only [h320, h321, h331, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h334 | h334
                    · linarith only [h314, h334, hlam]
                    · linarith only [h320, h321, h334, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h337 | h337
                · rcases m.htr 0 1 4 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h339 | h339
                    · linarith only [h314, h339, hlam]
                    · linarith only [h320, h339, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h342 | h342
                    · linarith only [h314, h342, hlam]
                    · linarith only [h320, h337, h342, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h346 | h346
                    · linarith only [h314, h346, hlam]
                    · linarith only [h320, h346, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h349 | h349
                    · linarith only [h314, h349, hlam]
                    · linarith only [h320, h349, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h352 | h352
              · rcases m.htr 0 1 3 (by decide) (by decide) with h353 | h353
                · rcases m.htr 0 1 4 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h355 | h355
                    · linarith only [h314, h355, hlam]
                    · linarith only [h319, h352, h355, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h358 | h358
                    · linarith only [h314, h358, hlam]
                    · linarith only [h319, h352, h358, hc12, hc35, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
                    · linarith only [h314, h362, hlam]
                    · linarith only [h319, h352, h362, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h365 | h365
                    · linarith only [h314, h365, hlam]
                    · linarith only [h319, h352, h365, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h368 | h368
                · rcases m.htr 0 1 4 (by decide) (by decide) with h369 | h369
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h370 | h370
                    · linarith only [h314, h370, hlam]
                    · linarith only [h319, h370, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h373 | h373
                    · linarith only [h314, h373, hlam]
                    · linarith only [h319, h368, h373, hc13, hc35, hlam, hphi, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h377 | h377
                    · linarith only [h314, h377, hlam]
                    · linarith only [h319, h377, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h380 | h380
                    · linarith only [h314, h380, hlam]
                    · linarith only [h319, h380, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h383 | h383
            · rcases m.htr 0 1 2 (by decide) (by decide) with h384 | h384
              · rcases m.htr 0 1 3 (by decide) (by decide) with h385 | h385
                · rcases m.htr 0 1 4 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h387 | h387
                    · linarith only [h314, h387, hlam]
                    · linarith only [h383, h384, h387, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h390 | h390
                    · linarith only [h314, h390, hlam]
                    · linarith only [h383, h384, h390, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h393 | h393
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h394 | h394
                    · linarith only [h314, h394, hlam]
                    · linarith only [h383, h384, h394, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h397 | h397
                    · linarith only [h314, h397, hlam]
                    · linarith only [h383, h384, h397, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h400 | h400
                · rcases m.htr 0 1 4 (by decide) (by decide) with h401 | h401
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h402 | h402
                    · linarith only [h314, h402, hlam]
                    · linarith only [h383, h402, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h405 | h405
                    · linarith only [h314, h405, hlam]
                    · linarith only [h383, h400, h405, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h408 | h408
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h409 | h409
                    · linarith only [h314, h409, hlam]
                    · linarith only [h383, h409, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h412 | h412
                    · linarith only [h314, h412, hlam]
                    · linarith only [h383, h412, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h415 | h415
              · rcases m.htr 0 1 3 (by decide) (by decide) with h416 | h416
                · rcases m.htr 0 1 4 (by decide) (by decide) with h417 | h417
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h418 | h418
                    · linarith only [h314, h418, hlam]
                    · linarith only [h415, h418, hc12, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h314, h421, hlam]
                    · linarith only [h415, h421, hc12, hc25, hlam, hphi, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h424 | h424
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h425 | h425
                    · linarith only [h314, h425, hlam]
                    · linarith only [h415, h425, hc12, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h428 | h428
                    · linarith only [h314, h428, hlam]
                    · linarith only [h415, h428, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h431 | h431
                · rcases m.htr 0 1 4 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h433 | h433
                    · linarith only [h314, h433, hlam]
                    · linarith only [h433, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h436 | h436
                    · linarith only [h314, h436, hlam]
                    · linarith only [h431, h436, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h439 | h439
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
                    · linarith only [h314, h440, hlam]
                    · linarith only [h440, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h443 | h443
                    · linarith only [h314, h443, hlam]
                    · linarith only [h443, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h318, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h448 | h448
    · linarith only [h448, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · rcases p0_3 (m.d 1 5) (by simp) with h450 | h450
      · linarith only [h450, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi3]
      · rcases p0_3 (m.d 2 5) (by simp) with h452 | h452
        · rcases p0_3 (m.d 3 5) (by simp) with h453 | h453
          · linarith only [h453, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h455 | h455
            · rcases m.htr 0 1 2 (by decide) (by decide) with h456 | h456
              · rcases m.htr 0 1 3 (by decide) (by decide) with h457 | h457
                · rcases m.htr 0 1 4 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h460 | h460
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h461 | h461
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h462 | h462
                          · linarith only [h448, h459, h462, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h448, h455, h460, h462, hc23, hc45, hlam, hphi, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h465 | h465
                          · linarith only [h448, h459, h465, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h448, h455, h460, h465, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h468 | h468
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h469 | h469
                          · linarith only [h448, h459, h469, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h448, h455, h468, h469, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h472 | h472
                          · linarith only [h448, h472, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h474 | h474
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h475 | h475
                              · linarith only [h448, h475, hlam]
                              · linarith only [h455, h475, hc03, hc45, hlam, hphi, ht34, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h478 | h478
                              · linarith only [h448, h478, hlam]
                              · linarith only [h455, h460, h478, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h450, h455, h459, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h482 | h482
                    · linarith only [h458, h482, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h455, h482, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h485 | h485
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h486 | h486
                    · linarith only [h457, h486, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h450, h455, h486, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h489 | h489
                    · linarith only [h485, h489, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h455, h489, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h492 | h492
                · rcases m.htr 0 1 4 (by decide) (by decide) with h493 | h493
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h494 | h494
                    · linarith only [h456, h494, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h450, h455, h494, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h497 | h497
                    · linarith only [h493, h497, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h455, h497, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h500 | h500
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h501 | h501
                    · linarith only [h492, h501, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h450, h455, h501, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h504 | h504
                    · linarith only [h500, h504, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h455, h504, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h507 | h507
              · rcases m.htr 0 1 3 (by decide) (by decide) with h508 | h508
                · rcases m.htr 0 1 4 (by decide) (by decide) with h509 | h509
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h510 | h510
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h511 | h511
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h512 | h512
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h513 | h513
                          · linarith only [h513, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h515 | h515
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h516 | h516
                              · linarith only [h448, h516, hlam]
                              · linarith only [h515, h516, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h519 | h519
                              · linarith only [h448, h519, hlam]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h521 | h521
                                · linarith only [h512, h513, h519, h521, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h525 | h525
                                      · linarith only [h507, h513, h519, h525, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                                        · linarith only [h450, h527, hlam]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
                                          · linarith only [h509, h521, h529, hlam]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
                                            · linarith only [h507, h513, h515, h519, h523, h531, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h533 | h533
                                              · linarith only [h455, h508, h521, h523, h533, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                              · linarith only [h533, hlam, p0_0]
                                    · linarith only [h512, h523, h524, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h511, h513, h519, h523, hc12, hc25, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h538 | h538
                          · linarith only [h538, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h540 | h540
                            · linarith only [h511, h512, h540, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h542 | h542
                              · linarith only [h448, h542, hlam]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h544 | h544
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                                    · linarith only [h507, h512, h546, hlam]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                                      · linarith only [h507, h538, h542, h548, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                                        · linarith only [h450, h550, hlam]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
                                          · linarith only [h509, h552, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                                          · linarith only [h544, h545, h546, h552, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                                  · linarith only [h511, h538, h542, h545, hc12, hc25, hlam, hphi, p0_1]
                                · linarith only [h455, h511, h512, h544, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h557 | h557
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h558 | h558
                          · linarith only [h558, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h560 | h560
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h561 | h561
                              · linarith only [h448, h561, hlam]
                              · linarith only [h511, h561, hc02, hc25, hlam, hphi, p0_1]
                            · linarith only [h511, h557, h560, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h565 | h565
                          · linarith only [h565, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h568 | h568
                              · linarith only [h448, h568, hlam]
                              · linarith only [h567, h568, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                              · linarith only [h448, h571, hlam]
                              · linarith only [h511, h571, hc02, hc25, hlam, hphi, p0_1]
                    · linarith only [h450, h510, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h575 | h575
                    · linarith only [h509, h575, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h575, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h578 | h578
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h579 | h579
                    · linarith only [h508, h579, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h450, h579, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h582 | h582
                    · linarith only [h578, h582, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h582, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h585 | h585
                · rcases m.htr 0 1 4 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h587 | h587
                    · linarith only [h507, h587, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h450, h587, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h590 | h590
                    · linarith only [h586, h590, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h590, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h593 | h593
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h594 | h594
                    · linarith only [h585, h594, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h450, h594, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h597 | h597
                    · linarith only [h593, h597, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h450, h597, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h452, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h601 | h601
    · linarith only [h601, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · rcases p0_3 (m.d 1 5) (by simp) with h603 | h603
      · linarith only [h603, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi4]
      · rcases p0_3 (m.d 2 5) (by simp) with h605 | h605
        · rcases p0_3 (m.d 3 5) (by simp) with h606 | h606
          · rcases p0_3 (m.d 4 5) (by simp) with h607 | h607
            · linarith only [h607, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h609 | h609
              · rcases m.htr 0 1 3 (by decide) (by decide) with h610 | h610
                · rcases m.htr 0 1 4 (by decide) (by decide) with h611 | h611
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h612 | h612
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h613 | h613
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h614 | h614
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h615 | h615
                          · linarith only [h601, h609, h612, h615, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
                          · linarith only [h601, h606, h613, h615, hc23, hc35, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h618 | h618
                          · linarith only [h601, h618, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · linarith only [h601, h606, h613, h618, hc23, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h621 | h621
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h622 | h622
                          · linarith only [h601, h622, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h624 | h624
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h625 | h625
                              · linarith only [h601, h606, h610, h622, h625, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h627 | h627
                                · linarith only [h601, h627, hlam]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
                                  · linarith only [h606, h609, h613, h625, h627, h629, hc23, hc35, hlam, hphi, p0_1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h631 | h631
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h632 | h632
                                      · linarith only [h609, h613, h625, h627, h632, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
                                        · linarith only [h606, h610, h625, h627, h634, hlam, p0_1]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                                          · linarith only [h603, h636, hlam]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h638 | h638
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h639 | h639
                                              · linarith only [h606, h639, hlam]
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h641 | h641
                                                · linarith only [h609, h613, h625, h627, h631, h641, hlam]
                                                · linarith only [h641, hlam, p0_0]
                                            · linarith only [h609, h613, h624, h631, h638, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · linarith only [h606, h613, h621, h625, h627, h631, hc12, hc35, hlam, hphi, ht23, p0_1]
                            · linarith only [h613, h621, h624, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h647 | h647
                          · linarith only [h647, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi4]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h649 | h649
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h650 | h650
                              · linarith only [h601, h606, h610, h647, h650, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h652 | h652
                                · linarith only [h601, h652, hlam]
                                · linarith only [h606, h609, h621, h652, hc12, hc35, hlam, hphi, ht23, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h655 | h655
                              · linarith only [h606, h655, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi4]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
                                · linarith only [h601, h657, hlam]
                                · linarith only [h609, h621, h657, hc12, hc25, hlam, hphi, p0_1]
                    · linarith only [h603, h606, h612, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h661 | h661
                    · linarith only [h611, h661, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h606, h661, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h665 | h665
                    · linarith only [h610, h665, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h603, h665, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h668 | h668
                    · linarith only [h664, h668, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h606, h668, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h671 | h671
                · rcases m.htr 0 1 4 (by decide) (by decide) with h672 | h672
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h673 | h673
                    · linarith only [h609, h673, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h603, h606, h673, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h676 | h676
                    · linarith only [h672, h676, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h606, h676, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h679 | h679
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h680 | h680
                    · linarith only [h671, h680, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h603, h606, h680, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h683 | h683
                    · linarith only [h679, h683, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h606, h683, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h686 | h686
            · linarith only [h686, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h688 | h688
              · rcases m.htr 0 1 3 (by decide) (by decide) with h689 | h689
                · rcases m.htr 0 1 4 (by decide) (by decide) with h690 | h690
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h691 | h691
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h692 | h692
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h693 | h693
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h694 | h694
                          · linarith only [h606, h688, h694, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h696 | h696
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h697 | h697
                              · linarith only [h601, h692, h694, h697, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi3]
                              · linarith only [h606, h696, h697, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h700 | h700
                              · linarith only [h601, h692, h694, h700, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi3]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h702 | h702
                                · linarith only [h601, h702, hlam]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h706 | h706
                                      · linarith only [h606, h688, h694, h700, h706, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h708 | h708
                                        · linarith only [h688, h689, h694, h696, h700, h702, h704, h708, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h710 | h710
                                          · linarith only [h603, h710, hlam]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                                            · linarith only [h688, h696, h704, h712, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                                              · linarith only [h689, h700, h704, h714, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                                              · linarith only [h696, h702, h714, hc03, hc35, hlam, hphi, p0_1]
                                    · linarith only [h693, h694, h702, h705, hc12, hc25, hlam, hphi, p0_1]
                                  · linarith only [h692, h694, h702, h704, hc12, hc25, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h719 | h719
                          · linarith only [h606, h719, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h721 | h721
                            · linarith only [h692, h693, h721, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h723 | h723
                              · linarith only [h601, h692, h719, h723, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi3]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h725 | h725
                                · linarith only [h601, h725, hlam]
                                · linarith only [h692, h693, h725, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h728 | h728
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h729 | h729
                          · linarith only [h606, h729, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h731 | h731
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h732 | h732
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
                                · linarith only [h601, h733, hlam]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h735 | h735
                                  · linarith only [h688, h692, h735, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h737 | h737
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h738 | h738
                                      · linarith only [h688, h729, h733, h738, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h740 | h740
                                        · linarith only [h689, h740, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                                        · linarith only [h732, h733, h735, h740, hc12, hc25, hlam, hphi, p0_1]
                                    · linarith only [h728, h729, h733, h737, hc12, hc25, hlam, hphi, p0_1]
                              · linarith only [h606, h692, h732, hc02, hc25, hlam, hphi, p0_1]
                            · linarith only [h692, h728, h731, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h746 | h746
                          · linarith only [h606, h746, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi3]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h748 | h748
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h749 | h749
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                                · linarith only [h601, h750, hlam]
                                · linarith only [h728, h750, hc02, hc25, hlam, hphi, p0_1]
                              · linarith only [h606, h688, h692, h749, hc12, hc25, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h754 | h754
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h755 | h755
                                · linarith only [h601, h755, hlam]
                                · linarith only [h748, h754, h755, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi3]
                              · linarith only [h606, h688, h692, h754, hc12, hc25, hlam, hphi, p0_1]
                    · linarith only [h603, h691, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h760 | h760
                    · linarith only [h690, h760, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h760, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h763 | h763
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h764 | h764
                    · linarith only [h689, h764, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h603, h764, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h767 | h767
                    · linarith only [h763, h767, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h767, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h770 | h770
                · rcases m.htr 0 1 4 (by decide) (by decide) with h771 | h771
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h772 | h772
                    · linarith only [h688, h772, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h603, h772, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h775 | h775
                    · linarith only [h771, h775, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h775, hc01, hc25, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h778 | h778
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h779 | h779
                    · linarith only [h770, h779, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h603, h779, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h782 | h782
                    · linarith only [h778, h782, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h603, h782, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h605, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h786 | h786
    · linarith only [h786, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h788 | h788
      · linarith only [h788, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi0]
      · rcases p0_3 (m.d 2 5) (by simp) with h790 | h790
        · rcases p0_3 (m.d 3 5) (by simp) with h791 | h791
          · rcases p0_3 (m.d 4 5) (by simp) with h792 | h792
            · rcases m.htr 0 1 2 (by decide) (by decide) with h793 | h793
              · rcases m.htr 0 1 3 (by decide) (by decide) with h794 | h794
                · rcases m.htr 0 1 4 (by decide) (by decide) with h795 | h795
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h796 | h796
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h797 | h797
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h798 | h798
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h799 | h799
                          · linarith only [h790, h793, h796, h799, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
                          · linarith only [h792, h798, h799, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h802 | h802
                          · linarith only [h790, h796, h802, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h792, h797, h802, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h805 | h805
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h806 | h806
                          · linarith only [h790, h796, h806, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h792, h805, h806, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h809 | h809
                          · linarith only [h790, h796, h809, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h811 | h811
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h812 | h812
                              · linarith only [h812, hlam, p0_0]
                              · linarith only [h792, h811, h812, hc34, hc45, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h815 | h815
                              · linarith only [h815, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h817 | h817
                                · linarith only [h792, h796, h817, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi1]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h819 | h819
                                  · linarith only [h792, h793, h797, h811, h817, h819, hc23, hc45, hlam, hphi, ht34, p0_1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h821 | h821
                                    · linarith only [h793, h805, h821, hlam]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h823 | h823
                                      · linarith only [h790, h793, h797, h811, h817, h823, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h825 | h825
                                        · linarith only [h794, h811, h817, h825, hlam, p0_1]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h827 | h827
                                          · linarith only [h792, h795, h817, h827, hlam, p0_1]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h829 | h829
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h830 | h830
                                              · linarith only [h796, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi1]
                                              · linarith only [h790, h830, hlam]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
                                              · linarith only [h796, h833, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi1]
                                              · linarith only [h790, h833, hlam]
                    · linarith only [h788, h796, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h837 | h837
                    · linarith only [h795, h837, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h788, h837, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h840 | h840
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h841 | h841
                    · linarith only [h794, h841, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h788, h841, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h844 | h844
                    · linarith only [h794, h844, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h788, h844, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h847 | h847
                · rcases m.htr 0 1 4 (by decide) (by decide) with h848 | h848
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h849 | h849
                    · linarith only [h793, h849, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h849, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h852 | h852
                    · linarith only [h793, h852, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h852, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h855 | h855
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h856 | h856
                    · linarith only [h793, h856, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h856, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h859 | h859
                    · linarith only [h793, h859, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h859, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h862 | h862
              · rcases m.htr 0 1 3 (by decide) (by decide) with h863 | h863
                · rcases m.htr 0 1 4 (by decide) (by decide) with h864 | h864
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h865 | h865
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h866 | h866
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h867 | h867
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h868 | h868
                          · linarith only [h790, h862, h868, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
                          · linarith only [h866, h868, hc23, hc35, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h871 | h871
                          · linarith only [h790, h871, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · linarith only [h866, h871, hc23, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h874 | h874
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h875 | h875
                          · linarith only [h790, h875, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h877 | h877
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h878 | h878
                              · linarith only [h878, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h880 | h880
                                · linarith only [h866, h874, h878, h880, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                · linarith only [h792, h880, hlam]
                            · linarith only [h866, h874, h877, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h884 | h884
                          · linarith only [h790, h884, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h886 | h886
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h887 | h887
                              · linarith only [h887, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h889 | h889
                                · linarith only [h886, h887, h889, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                · linarith only [h792, h889, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h892 | h892
                              · linarith only [h892, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h894 | h894
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                                  · linarith only [h862, h866, h895, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h897 | h897
                                    · linarith only [h862, h874, h894, h897, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h899 | h899
                                      · linarith only [h790, h862, h866, h892, h899, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h901 | h901
                                        · linarith only [h863, h892, h901, hlam, p0_1]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h903 | h903
                                          · linarith only [h864, h903, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                                          · linarith only [h894, h897, h903, hc12, hc35, hlam, hphi, ht23, p0_1]
                                · linarith only [h792, h894, hlam]
                    · linarith only [h788, h865, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h908 | h908
                    · linarith only [h864, h908, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h788, h908, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h911 | h911
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h912 | h912
                    · linarith only [h863, h912, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h788, h912, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h915 | h915
                    · linarith only [h863, h915, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h788, h915, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h918 | h918
                · rcases m.htr 0 1 4 (by decide) (by decide) with h919 | h919
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h920 | h920
                    · linarith only [h862, h920, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h920, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h923 | h923
                    · linarith only [h862, h923, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h923, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h926 | h926
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h927 | h927
                    · linarith only [h862, h927, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h927, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h930 | h930
                    · linarith only [h862, h930, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h930, hlam]
          · linarith only [h791, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h934 | h934
          · rcases p0_3 (m.d 4 5) (by simp) with h935 | h935
            · rcases m.htr 0 1 2 (by decide) (by decide) with h936 | h936
              · rcases m.htr 0 1 3 (by decide) (by decide) with h937 | h937
                · rcases m.htr 0 1 4 (by decide) (by decide) with h938 | h938
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h939 | h939
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h940 | h940
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h941 | h941
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h942 | h942
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h943 | h943
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h944 | h944
                              · linarith only [h944, hlam, p0_0]
                              · linarith only [h935, h943, h944, hc34, hc45, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h947 | h947
                              · linarith only [h947, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h949 | h949
                                · linarith only [h935, h949, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi0]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h951 | h951
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h952 | h952
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h953 | h953
                                      · linarith only [h936, h953, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                                      · linarith only [h935, h939, h942, h952, h953, hc24, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                                    · linarith only [h935, h936, h939, h941, h951, h952, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p0_1, u1elo0, u5ehi1]
                                  · linarith only [h935, h940, h943, h949, h951, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                          · linarith only [h790, h942, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h959 | h959
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h960 | h960
                            · linarith only [h940, h941, h960, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h962 | h962
                              · linarith only [h962, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h964 | h964
                                · linarith only [h935, h939, h964, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi1]
                                · linarith only [h935, h940, h941, h964, hc23, hc45, hlam, hphi, ht34, p0_1]
                          · linarith only [h790, h959, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h968 | h968
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h969 | h969
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h970 | h970
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h971 | h971
                              · linarith only [h971, hlam, p0_0]
                              · linarith only [h935, h940, h969, h971, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                            · linarith only [h940, h968, h970, hlam]
                          · linarith only [h790, h969, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h976 | h976
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h977 | h977
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h978 | h978
                              · linarith only [h978, hlam, p0_0]
                              · linarith only [h935, h977, h978, hc34, hc45, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h981 | h981
                              · linarith only [h981, hlam, p0_0]
                              · linarith only [h935, h940, h976, h981, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                          · linarith only [h790, h976, hlam]
                    · linarith only [h788, h939, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h986 | h986
                    · linarith only [h938, h986, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h788, h986, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h989 | h989
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h990 | h990
                    · linarith only [h937, h990, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h788, h990, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h993 | h993
                    · linarith only [h937, h993, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h788, h993, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h996 | h996
                · rcases m.htr 0 1 4 (by decide) (by decide) with h997 | h997
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h998 | h998
                    · linarith only [h936, h998, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h788, h998, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1001 | h1001
                    · linarith only [h1001, h936, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1001, h788, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1004 | h1004
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1005 | h1005
                    · linarith only [h1005, h936, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1005, h788, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1008 | h1008
                    · linarith only [h1008, h936, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1008, h788, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1012 | h1012
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1013 | h1013
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1014 | h1014
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1015 | h1015
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1016 | h1016
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1017 | h1017
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1018 | h1018
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1019 | h1019
                              · linarith only [h1019, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1021 | h1021
                                · linarith only [h1018, h1019, h1021, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                · linarith only [h1021, h935, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1024 | h1024
                              · linarith only [h1024, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1026 | h1026
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1027 | h1027
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1028 | h1028
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1029 | h1029
                                      · linarith only [h1011, h1029, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                                      · linarith only [h1017, h1029, hc12, hc35, hlam, hphi, ht23, p0_1]
                                    · linarith only [h1016, h1027, h1028, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h1015, h1024, h1027, hc12, hc35, hlam, hphi, ht23, p0_1]
                                · linarith only [h1026, h935, hlam]
                          · linarith only [h1017, h790, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1036 | h1036
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1037 | h1037
                            · linarith only [h1015, h1016, h1037, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1039 | h1039
                              · linarith only [h1039, hlam, p0_0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1041 | h1041
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1042 | h1042
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1043 | h1043
                                    · linarith only [h1011, h1016, h1036, h1043, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1045 | h1045
                                      · linarith only [h1013, h1043, h1045, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                                      · linarith only [h1036, h1042, h1045, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h1015, h1016, h1042, hc12, hc24, hlam, hphi]
                                · linarith only [h1041, h935, hlam]
                          · linarith only [h1036, h790, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1051 | h1051
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1052 | h1052
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1053 | h1053
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1054 | h1054
                              · linarith only [h1054, hlam, p0_0]
                              · linarith only [h1015, h1052, h1054, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                            · linarith only [h1015, h1051, h1053, hlam]
                          · linarith only [h1052, h790, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1059 | h1059
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1060 | h1060
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1061 | h1061
                              · linarith only [h1061, hlam, p0_0]
                              · linarith only [h1051, h1059, h1060, h1061, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1064 | h1064
                              · linarith only [h1064, hlam, p0_0]
                              · linarith only [h1015, h1059, h1064, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                          · linarith only [h1059, h790, hlam]
                    · linarith only [h1014, h788, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1069 | h1069
                    · linarith only [h1013, h1069, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1069, h788, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1072 | h1072
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1073 | h1073
                    · linarith only [h1012, h1073, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1073, h788, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1076 | h1076
                    · linarith only [h1012, h1076, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1076, h788, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1079 | h1079
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1080 | h1080
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1081 | h1081
                    · linarith only [h1011, h1081, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1081, h788, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1084 | h1084
                    · linarith only [h1011, h1084, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1084, h788, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1087 | h1087
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1088 | h1088
                    · linarith only [h1011, h1088, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1088, h788, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1091 | h1091
                    · linarith only [h1011, h1091, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1091, h788, hlam]
          · linarith only [h934, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1095 | h1095
    · linarith only [h1095, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · rcases p0_3 (m.d 1 5) (by simp) with h1097 | h1097
      · linarith only [h1097, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1099 | h1099
        · rcases p0_3 (m.d 3 5) (by simp) with h1100 | h1100
          · rcases p0_3 (m.d 4 5) (by simp) with h1101 | h1101
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1102 | h1102
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1103 | h1103
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1104 | h1104
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1105 | h1105
                    · linarith only [h1095, h1105, hlam]
                    · linarith only [h1101, h1105, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1108 | h1108
                    · linarith only [h1095, h1108, hlam]
                    · linarith only [h1101, h1102, h1108, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1111 | h1111
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1112 | h1112
                    · linarith only [h1095, h1112, hlam]
                    · linarith only [h1101, h1102, h1112, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1115 | h1115
                    · linarith only [h1095, h1115, hlam]
                    · linarith only [h1101, h1102, h1115, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1118 | h1118
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1119 | h1119
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1120 | h1120
                    · linarith only [h1095, h1120, hlam]
                    · linarith only [h1101, h1120, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1123 | h1123
                    · linarith only [h1095, h1123, hlam]
                    · linarith only [h1101, h1118, h1123, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1126 | h1126
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1127 | h1127
                    · linarith only [h1095, h1127, hlam]
                    · linarith only [h1101, h1127, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1130 | h1130
                    · linarith only [h1095, h1130, hlam]
                    · linarith only [h1101, h1130, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1133 | h1133
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1134 | h1134
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1135 | h1135
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1136 | h1136
                    · linarith only [h1095, h1136, hlam]
                    · linarith only [h1133, h1136, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1139 | h1139
                    · linarith only [h1095, h1139, hlam]
                    · linarith only [h1133, h1139, hc12, hc35, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1142 | h1142
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1143 | h1143
                    · linarith only [h1095, h1143, hlam]
                    · linarith only [h1133, h1143, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1146 | h1146
                    · linarith only [h1095, h1146, hlam]
                    · linarith only [h1133, h1146, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1149 | h1149
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1150 | h1150
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1151 | h1151
                    · linarith only [h1095, h1151, hlam]
                    · linarith only [h1151, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1154 | h1154
                    · linarith only [h1095, h1154, hlam]
                    · linarith only [h1149, h1154, hc13, hc35, hlam, hphi, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1157 | h1157
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1158 | h1158
                    · linarith only [h1095, h1158, hlam]
                    · linarith only [h1158, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1161 | h1161
                    · linarith only [h1095, h1161, hlam]
                    · linarith only [h1161, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1100, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1165 | h1165
          · rcases p0_3 (m.d 4 5) (by simp) with h1166 | h1166
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1167 | h1167
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1168 | h1168
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1169 | h1169
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1170 | h1170
                    · linarith only [h1095, h1170, hlam]
                    · linarith only [h1166, h1167, h1170, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1173 | h1173
                    · linarith only [h1095, h1173, hlam]
                    · linarith only [h1166, h1167, h1173, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1176 | h1176
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1177 | h1177
                    · linarith only [h1095, h1177, hlam]
                    · linarith only [h1166, h1167, h1177, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1180 | h1180
                    · linarith only [h1095, h1180, hlam]
                    · linarith only [h1166, h1167, h1180, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1183 | h1183
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1184 | h1184
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1185 | h1185
                    · linarith only [h1095, h1185, hlam]
                    · linarith only [h1166, h1185, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1188 | h1188
                    · linarith only [h1095, h1188, hlam]
                    · linarith only [h1166, h1183, h1188, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1191 | h1191
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1192 | h1192
                    · linarith only [h1095, h1192, hlam]
                    · linarith only [h1166, h1192, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1195 | h1195
                    · linarith only [h1095, h1195, hlam]
                    · linarith only [h1166, h1195, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1198 | h1198
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1199 | h1199
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1200 | h1200
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1201 | h1201
                    · linarith only [h1095, h1201, hlam]
                    · linarith only [h1198, h1201, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1204 | h1204
                    · linarith only [h1095, h1204, hlam]
                    · linarith only [h1198, h1204, hc12, hc35, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1207 | h1207
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1208 | h1208
                    · linarith only [h1095, h1208, hlam]
                    · linarith only [h1198, h1208, hc12, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1211 | h1211
                    · linarith only [h1095, h1211, hlam]
                    · linarith only [h1198, h1211, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1214 | h1214
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1215 | h1215
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1216 | h1216
                    · linarith only [h1095, h1216, hlam]
                    · linarith only [h1216, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1219 | h1219
                    · linarith only [h1095, h1219, hlam]
                    · linarith only [h1214, h1219, hc13, hc35, hlam, hphi, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1222 | h1222
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1223 | h1223
                    · linarith only [h1095, h1223, hlam]
                    · linarith only [h1223, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1226 | h1226
                    · linarith only [h1095, h1226, hlam]
                    · linarith only [h1226, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1165, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1230 | h1230
    · linarith only [h1230, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
    · rcases p0_3 (m.d 1 5) (by simp) with h1232 | h1232
      · linarith only [h1232, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi2]
      · rcases p0_3 (m.d 2 5) (by simp) with h1234 | h1234
        · linarith only [h1234, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1236 | h1236
          · rcases p0_3 (m.d 4 5) (by simp) with h1237 | h1237
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1238 | h1238
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1239 | h1239
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1240 | h1240
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1241 | h1241
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1242 | h1242
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1243 | h1243
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1244 | h1244
                          · linarith only [h1230, h1244, hlam]
                          · linarith only [h1242, h1244, hc23, hc35, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1247 | h1247
                          · linarith only [h1230, h1247, hlam]
                          · linarith only [h1237, h1242, h1247, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1250 | h1250
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1251 | h1251
                          · linarith only [h1230, h1251, hlam]
                          · linarith only [h1237, h1251, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1254 | h1254
                          · linarith only [h1230, h1254, hlam]
                          · linarith only [h1237, h1238, h1254, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1232, h1237, h1241, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1258 | h1258
                    · linarith only [h1240, h1258, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1232, h1237, h1258, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1261 | h1261
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1262 | h1262
                    · linarith only [h1239, h1262, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1232, h1237, h1262, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1265 | h1265
                    · linarith only [h1261, h1265, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1232, h1237, h1265, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1268 | h1268
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1269 | h1269
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1270 | h1270
                    · linarith only [h1238, h1270, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1232, h1237, h1270, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1273 | h1273
                    · linarith only [h1269, h1273, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1232, h1237, h1273, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1276 | h1276
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1277 | h1277
                    · linarith only [h1268, h1277, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1232, h1237, h1277, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1280 | h1280
                    · linarith only [h1268, h1280, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1232, h1237, h1280, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1283 | h1283
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1284 | h1284
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1285 | h1285
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1286 | h1286
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1287 | h1287
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1288 | h1288
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1289 | h1289
                          · linarith only [h1230, h1289, hlam]
                          · linarith only [h1289, hc02, hc35, hlam, hphi, ht23, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1292 | h1292
                          · linarith only [h1230, h1292, hlam]
                          · linarith only [h1287, h1292, hc23, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1295 | h1295
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1296 | h1296
                          · linarith only [h1230, h1296, hlam]
                          · linarith only [h1296, hc02, hc35, hlam, hphi, ht23, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1299 | h1299
                          · linarith only [h1230, h1299, hlam]
                          · linarith only [h1283, h1299, hc12, hc35, hlam, hphi, ht23, p0_1]
                    · linarith only [h1232, h1286, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1303 | h1303
                    · linarith only [h1285, h1303, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1232, h1303, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1306 | h1306
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1307 | h1307
                    · linarith only [h1284, h1307, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1232, h1307, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1310 | h1310
                    · linarith only [h1306, h1310, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1232, h1310, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1313 | h1313
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1314 | h1314
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1315 | h1315
                    · linarith only [h1283, h1315, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1232, h1315, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1318 | h1318
                    · linarith only [h1314, h1318, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1232, h1318, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1321 | h1321
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1322 | h1322
                    · linarith only [h1313, h1322, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1232, h1322, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1325 | h1325
                    · linarith only [h1321, h1325, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1232, h1325, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1330 | h1330
    · linarith only [h1330, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1332 | h1332
      · linarith only [h1332, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi4]
      · rcases p0_3 (m.d 2 5) (by simp) with h1334 | h1334
        · rcases p0_3 (m.d 3 5) (by simp) with h1335 | h1335
          · rcases p0_3 (m.d 4 5) (by simp) with h1336 | h1336
            · linarith only [h1336, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1338 | h1338
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1339 | h1339
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1340 | h1340
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1341 | h1341
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1342 | h1342
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1343 | h1343
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1344 | h1344
                          · linarith only [h1330, h1334, h1341, h1344, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h1330, h1342, h1344, hc23, hc35, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1347 | h1347
                          · linarith only [h1330, h1334, h1347, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · linarith only [h1330, h1342, h1347, hc23, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1350 | h1350
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1351 | h1351
                          · linarith only [h1330, h1334, h1351, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1353 | h1353
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1354 | h1354
                              · linarith only [h1330, h1339, h1351, h1354, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1356 | h1356
                                · linarith only [h1330, h1356, hlam]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1358 | h1358
                                  · linarith only [h1338, h1342, h1354, h1356, h1358, hc23, hc35, hlam, hphi, p0_1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1360 | h1360
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1361 | h1361
                                      · linarith only [h1334, h1338, h1342, h1354, h1356, h1361, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1363 | h1363
                                        · linarith only [h1338, h1342, h1354, h1356, h1360, h1363, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1365 | h1365
                                          · linarith only [h1332, h1365, hlam]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1367 | h1367
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1368 | h1368
                                              · linarith only [h1338, h1342, h1354, h1356, h1360, h1367, h1368, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                                              · linarith only [h1334, h1368, hlam]
                                            · linarith only [h1338, h1342, h1353, h1354, h1356, h1360, h1367, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                                    · linarith only [h1342, h1350, h1360, hc12, hc23, hlam, hphi]
                            · linarith only [h1342, h1350, h1353, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1374 | h1374
                          · linarith only [h1330, h1334, h1374, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1376 | h1376
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1377 | h1377
                              · linarith only [h1330, h1339, h1374, h1377, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1379 | h1379
                                · linarith only [h1330, h1379, hlam]
                                · linarith only [h1338, h1350, h1379, hc12, hc35, hlam, hphi, ht23, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1382 | h1382
                              · linarith only [h1382, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi4]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1384 | h1384
                                · linarith only [h1330, h1384, hlam]
                                · linarith only [h1338, h1350, h1384, hc12, hc35, hlam, hphi, ht23, p0_1]
                    · linarith only [h1332, h1341, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1388 | h1388
                    · linarith only [h1340, h1388, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1388, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1391 | h1391
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1392 | h1392
                    · linarith only [h1339, h1392, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1332, h1392, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1395 | h1395
                    · linarith only [h1391, h1395, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1395, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1398 | h1398
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1399 | h1399
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1400 | h1400
                    · linarith only [h1338, h1400, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1332, h1400, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1403 | h1403
                    · linarith only [h1399, h1403, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1403, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1406 | h1406
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1407 | h1407
                    · linarith only [h1398, h1407, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1332, h1407, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1410 | h1410
                    · linarith only [h1406, h1410, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1410, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1335, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1414 | h1414
          · rcases p0_3 (m.d 4 5) (by simp) with h1415 | h1415
            · linarith only [h1415, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1417 | h1417
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1418 | h1418
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1419 | h1419
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1420 | h1420
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1421 | h1421
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1422 | h1422
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1423 | h1423
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1424 | h1424
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1425 | h1425
                              · linarith only [h1425, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi4]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1427 | h1427
                                · linarith only [h1330, h1427, hlam]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                                      · linarith only [h1417, h1431, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                                      · linarith only [h1334, h1431, hc12, hc35, hlam, hphi, ht23, p0_1]
                                    · linarith only [h1417, h1422, h1429, h1430, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h1421, h1425, h1427, h1429, hc12, hc35, hlam, hphi, ht23, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1436 | h1436
                              · linarith only [h1330, h1436, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1438 | h1438
                                · linarith only [h1330, h1438, hlam]
                                · linarith only [h1424, h1438, hc03, hc35, hlam, hphi, p0_1]
                          · linarith only [h1334, h1421, h1423, hc23, hc35, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1442 | h1442
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1443 | h1443
                            · linarith only [h1421, h1422, h1443, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1445 | h1445
                              · linarith only [h1419, h1421, h1422, h1445, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi4]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1447 | h1447
                                · linarith only [h1330, h1447, hlam]
                                · linarith only [h1422, h1447, hc02, hc35, hlam, hphi, ht23, p0_1]
                          · linarith only [h1334, h1421, h1442, hc23, hc35, hlam, hphi, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1451 | h1451
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1452 | h1452
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1453 | h1453
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1454 | h1454
                              · linarith only [h1454, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi4]
                              · linarith only [h1330, h1421, h1452, h1454, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                            · linarith only [h1421, h1451, h1453, hlam]
                          · linarith only [h1334, h1452, hc02, hc35, hlam, hphi, ht23, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1459 | h1459
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1460 | h1460
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1461 | h1461
                              · linarith only [h1330, h1461, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi0]
                              · linarith only [h1330, h1421, h1459, h1461, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1464 | h1464
                              · linarith only [h1330, h1464, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi0]
                              · linarith only [h1330, h1421, h1459, h1464, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                          · linarith only [h1334, h1459, hc02, hc35, hlam, hphi, ht23, p0_1]
                    · linarith only [h1332, h1420, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1469 | h1469
                    · linarith only [h1419, h1469, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1469, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1472 | h1472
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1473 | h1473
                    · linarith only [h1418, h1473, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1332, h1473, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1476 | h1476
                    · linarith only [h1472, h1476, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1476, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1479 | h1479
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1480 | h1480
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1481 | h1481
                    · linarith only [h1417, h1481, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1332, h1481, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1484 | h1484
                    · linarith only [h1480, h1484, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1484, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1487 | h1487
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1488 | h1488
                    · linarith only [h1479, h1488, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1332, h1488, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1491 | h1491
                    · linarith only [h1487, h1491, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1332, h1491, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1414, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1495 | h1495
    · linarith only [h1495, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h1497 | h1497
      · linarith only [h1497, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1499 | h1499
        · rcases p0_3 (m.d 3 5) (by simp) with h1500 | h1500
          · rcases p0_3 (m.d 4 5) (by simp) with h1501 | h1501
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1502 | h1502
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1503 | h1503
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1504 | h1504
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1505 | h1505
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1506 | h1506
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1507 | h1507
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1508 | h1508
                          · linarith only [h1499, h1502, h1505, h1508, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
                          · linarith only [h1507, h1508, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1511 | h1511
                          · linarith only [h1499, h1511, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · linarith only [h1506, h1511, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1514 | h1514
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1515 | h1515
                          · linarith only [h1499, h1505, h1515, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h1514, h1515, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1518 | h1518
                          · linarith only [h1499, h1518, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1520 | h1520
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1521 | h1521
                              · linarith only [h1500, h1503, h1518, h1521, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0]
                              · linarith only [h1520, h1521, hc34, hc45, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1524 | h1524
                              · linarith only [h1500, h1505, h1524, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi1]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1526 | h1526
                                · linarith only [h1526, hlam, p0_0]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1528 | h1528
                                  · linarith only [h1502, h1506, h1528, hlam]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1530 | h1530
                                    · linarith only [h1502, h1514, h1530, hlam]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1532 | h1532
                                      · linarith only [h1499, h1502, h1506, h1520, h1526, h1532, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1534 | h1534
                                        · linarith only [h1500, h1505, h1534, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2, u5ehi1]
                                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1536 | h1536
                                          · linarith only [h1504, h1526, h1536, hlam, p0_1]
                                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1538 | h1538
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1539 | h1539
                                              · linarith only [h1500, h1505, h1539, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi1]
                                              · linarith only [h1506, h1520, h1538, h1539, hc02, hc35, hlam, hphi, ht23]
                                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1542 | h1542
                                              · linarith only [h1500, h1505, h1542, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi1]
                                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1544 | h1544
                                                · linarith only [h1505, h1538, h1544, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi1]
                                                · linarith only [h1499, h1544, hlam]
                    · linarith only [h1497, h1505, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1548 | h1548
                    · linarith only [h1504, h1548, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1497, h1548, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1551 | h1551
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1552 | h1552
                    · linarith only [h1503, h1552, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1552, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1555 | h1555
                    · linarith only [h1503, h1555, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1555, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1558 | h1558
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1559 | h1559
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1560 | h1560
                    · linarith only [h1502, h1560, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1560, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1563 | h1563
                    · linarith only [h1502, h1563, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1563, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1566 | h1566
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1567 | h1567
                    · linarith only [h1502, h1567, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1567, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1570 | h1570
                    · linarith only [h1502, h1570, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1570, hlam]
            · linarith only [h1501, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1574 | h1574
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1575 | h1575
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1576 | h1576
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1577 | h1577
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1578 | h1578
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1579 | h1579
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1580 | h1580
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1581 | h1581
                          · linarith only [h1499, h1575, h1578, h1581, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
                          · linarith only [h1579, h1581, hc23, hc45, hlam, hphi, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1584 | h1584
                          · linarith only [h1499, h1584, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · linarith only [h1579, h1584, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1587 | h1587
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1588 | h1588
                          · linarith only [h1499, h1578, h1588, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · linarith only [h1587, h1588, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1591 | h1591
                          · linarith only [h1499, h1578, h1591, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1593 | h1593
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1594 | h1594
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1595 | h1595
                                · linarith only [h1595, hlam, p0_0]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1597 | h1597
                                  · linarith only [h1575, h1587, h1595, h1597, hc23, hc45, hlam, hphi, ht34, p0_1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1599 | h1599
                                    · linarith only [h1575, h1587, h1599, hlam]
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1601 | h1601
                                      · linarith only [h1499, h1575, h1587, h1595, h1601, hlam, p0_1]
                                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1603 | h1603
                                        · linarith only [h1576, h1603, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                                        · linarith only [h1594, h1603, hc13, hc45, hlam, hphi, ht34, p0_1]
                              · linarith only [h1500, h1594, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1607 | h1607
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1608 | h1608
                                · linarith only [h1608, hlam, p0_0]
                                · linarith only [h1593, h1607, h1608, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi3]
                              · linarith only [h1500, h1607, hlam]
                    · linarith only [h1497, h1578, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1613 | h1613
                    · linarith only [h1577, h1613, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1497, h1613, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1616 | h1616
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1617 | h1617
                    · linarith only [h1576, h1617, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1617, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1620 | h1620
                    · linarith only [h1576, h1620, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1620, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1623 | h1623
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1624 | h1624
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1625 | h1625
                    · linarith only [h1575, h1625, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1625, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1628 | h1628
                    · linarith only [h1575, h1628, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1628, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1631 | h1631
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1632 | h1632
                    · linarith only [h1575, h1632, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1632, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1635 | h1635
                    · linarith only [h1575, h1635, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1635, hlam]
            · linarith only [h1574, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1639 | h1639
          · rcases p0_3 (m.d 4 5) (by simp) with h1640 | h1640
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1641 | h1641
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1642 | h1642
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1643 | h1643
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1644 | h1644
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1645 | h1645
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1646 | h1646
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1647 | h1647
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1648 | h1648
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1649 | h1649
                              · linarith only [h1639, h1641, h1645, h1649, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
                              · linarith only [h1648, h1649, hc34, hc45, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1652 | h1652
                              · linarith only [h1639, h1652, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi0]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1654 | h1654
                                · linarith only [h1654, hlam, p0_0]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1656 | h1656
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1657 | h1657
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1658 | h1658
                                      · linarith only [h1641, h1658, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                                      · linarith only [h1647, h1658, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                                    · linarith only [h1641, h1646, h1656, h1657, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h1645, h1648, h1654, h1656, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                          · linarith only [h1499, h1647, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1664 | h1664
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1665 | h1665
                            · linarith only [h1645, h1646, h1665, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1667 | h1667
                              · linarith only [h1639, h1645, h1646, h1664, h1667, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi2]
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1669 | h1669
                                · linarith only [h1669, hlam, p0_0]
                                · linarith only [h1646, h1664, h1669, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                          · linarith only [h1499, h1664, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1673 | h1673
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1674 | h1674
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1675 | h1675
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1676 | h1676
                              · linarith only [h1639, h1676, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi0]
                              · linarith only [h1675, h1676, hc34, hc45, hlam, hphi, p0_1]
                            · linarith only [h1645, h1673, h1675, hlam]
                          · linarith only [h1499, h1674, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1681 | h1681
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1682 | h1682
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1683 | h1683
                              · linarith only [h1639, h1642, h1683, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi0]
                              · linarith only [h1682, h1683, hc34, hc45, hlam, hphi, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1686 | h1686
                              · linarith only [h1639, h1644, h1686, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi1]
                              · linarith only [h1645, h1681, h1686, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                          · linarith only [h1499, h1681, hlam]
                    · linarith only [h1497, h1644, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1691 | h1691
                    · linarith only [h1643, h1691, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1497, h1691, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1694 | h1694
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1695 | h1695
                    · linarith only [h1642, h1695, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1695, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1698 | h1698
                    · linarith only [h1642, h1698, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1698, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1701 | h1701
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1702 | h1702
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1703 | h1703
                    · linarith only [h1641, h1703, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1703, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1706 | h1706
                    · linarith only [h1641, h1706, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1706, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1709 | h1709
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1710 | h1710
                    · linarith only [h1641, h1710, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1710, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1713 | h1713
                    · linarith only [h1641, h1713, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1713, hlam]
            · linarith only [h1640, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1717 | h1717
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1718 | h1718
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1719 | h1719
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1720 | h1720
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1721 | h1721
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1722 | h1722
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1723 | h1723
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1724 | h1724
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1725 | h1725
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1726 | h1726
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1727 | h1727
                                · linarith only [h1727, hlam, p0_0]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1729 | h1729
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1730 | h1730
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1731 | h1731
                                      · linarith only [h1718, h1731, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                                      · linarith only [h1724, h1731, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                                    · linarith only [h1723, h1729, h1730, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1735 | h1735
                                    · linarith only [h1718, h1721, h1722, h1729, h1735, hc24, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0, u5ehi1]
                                    · linarith only [h1723, h1727, h1735, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                              · linarith only [h1639, h1726, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1739 | h1739
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1740 | h1740
                                · linarith only [h1740, hlam, p0_0]
                                · linarith only [h1725, h1739, h1740, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi3]
                              · linarith only [h1639, h1739, hlam]
                          · linarith only [h1499, h1724, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1745 | h1745
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1746 | h1746
                            · linarith only [h1722, h1723, h1746, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1748 | h1748
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1749 | h1749
                                · linarith only [h1749, hlam, p0_0]
                                · linarith only [h1722, h1723, h1749, hc23, hc45, hlam, hphi, ht34, p0_1]
                              · linarith only [h1639, h1748, hlam]
                          · linarith only [h1499, h1745, hlam]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1754 | h1754
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1755 | h1755
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1756 | h1756
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1757 | h1757
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1758 | h1758
                                · linarith only [h1758, hlam, p0_0]
                                · rcases m.htr 1 2 3 (by decide) (by decide) with h1760 | h1760
                                  · linarith only [h1722, h1755, h1760, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1762 | h1762
                                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1763 | h1763
                                      · linarith only [h1719, h1760, h1763, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                                      · linarith only [h1722, h1755, h1763, hc12, hc23, hlam, hphi]
                                    · linarith only [h1722, h1754, h1762, hc12, hc23, hlam, hphi]
                              · linarith only [h1639, h1757, hlam]
                            · linarith only [h1722, h1754, h1756, hlam]
                          · linarith only [h1499, h1755, hlam]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1770 | h1770
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h1771 | h1771
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1772 | h1772
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1773 | h1773
                                · linarith only [h1773, hlam, p0_0]
                                · linarith only [h1754, h1770, h1773, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                              · linarith only [h1639, h1772, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h1777 | h1777
                              · rcases m.htr 0 4 5 (by decide) (by decide) with h1778 | h1778
                                · linarith only [h1778, hlam, p0_0]
                                · linarith only [h1722, h1770, h1771, h1778, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                              · linarith only [h1639, h1777, hlam]
                          · linarith only [h1499, h1770, hlam]
                    · linarith only [h1497, h1721, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1784 | h1784
                    · linarith only [h1720, h1784, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1497, h1784, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1787 | h1787
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1788 | h1788
                    · linarith only [h1719, h1788, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1788, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1791 | h1791
                    · linarith only [h1719, h1791, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1497, h1791, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1794 | h1794
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1795 | h1795
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1796 | h1796
                    · linarith only [h1718, h1796, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1796, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1799 | h1799
                    · linarith only [h1718, h1799, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1799, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1802 | h1802
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1803 | h1803
                    · linarith only [h1718, h1803, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1803, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1806 | h1806
                    · linarith only [h1718, h1806, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1497, h1806, hlam]
            · linarith only [h1717, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1810 | h1810
    · linarith only [h1810, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · rcases p0_3 (m.d 1 5) (by simp) with h1812 | h1812
      · linarith only [h1812, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1814 | h1814
        · rcases p0_3 (m.d 3 5) (by simp) with h1815 | h1815
          · rcases p0_3 (m.d 4 5) (by simp) with h1816 | h1816
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1817 | h1817
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1818 | h1818
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1819 | h1819
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1820 | h1820
                    · linarith only [h1810, h1820, hlam]
                    · linarith only [h1814, h1820, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1823 | h1823
                    · linarith only [h1810, h1823, hlam]
                    · linarith only [h1817, h1823, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1826 | h1826
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1827 | h1827
                    · linarith only [h1810, h1827, hlam]
                    · linarith only [h1817, h1827, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1830 | h1830
                    · linarith only [h1810, h1830, hlam]
                    · linarith only [h1817, h1830, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1833 | h1833
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1834 | h1834
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1835 | h1835
                    · linarith only [h1810, h1835, hlam]
                    · linarith only [h1835, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1838 | h1838
                    · linarith only [h1810, h1838, hlam]
                    · linarith only [h1833, h1838, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1841 | h1841
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h1810, h1842, hlam]
                    · linarith only [h1842, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1845 | h1845
                    · linarith only [h1810, h1845, hlam]
                    · linarith only [h1845, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1816, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1849 | h1849
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1850 | h1850
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1851 | h1851
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1852 | h1852
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1853 | h1853
                    · linarith only [h1810, h1853, hlam]
                    · linarith only [h1850, h1853, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1856 | h1856
                    · linarith only [h1810, h1856, hlam]
                    · linarith only [h1850, h1856, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1859 | h1859
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1860 | h1860
                    · linarith only [h1810, h1860, hlam]
                    · linarith only [h1850, h1860, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1863 | h1863
                    · linarith only [h1810, h1863, hlam]
                    · linarith only [h1850, h1863, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1866 | h1866
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1867 | h1867
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1868 | h1868
                    · linarith only [h1810, h1868, hlam]
                    · linarith only [h1868, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1871 | h1871
                    · linarith only [h1810, h1871, hlam]
                    · linarith only [h1866, h1871, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1874 | h1874
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1875 | h1875
                    · linarith only [h1810, h1875, hlam]
                    · linarith only [h1875, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1878 | h1878
                    · linarith only [h1810, h1878, hlam]
                    · linarith only [h1878, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1849, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1882 | h1882
          · rcases p0_3 (m.d 4 5) (by simp) with h1883 | h1883
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1884 | h1884
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1885 | h1885
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1886 | h1886
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1887 | h1887
                    · linarith only [h1810, h1887, hlam]
                    · linarith only [h1884, h1887, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1890 | h1890
                    · linarith only [h1810, h1890, hlam]
                    · linarith only [h1884, h1890, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1893 | h1893
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1894 | h1894
                    · linarith only [h1810, h1894, hlam]
                    · linarith only [h1884, h1894, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1897 | h1897
                    · linarith only [h1810, h1897, hlam]
                    · linarith only [h1884, h1897, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1900 | h1900
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1901 | h1901
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1902 | h1902
                    · linarith only [h1810, h1902, hlam]
                    · linarith only [h1902, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1905 | h1905
                    · linarith only [h1810, h1905, hlam]
                    · linarith only [h1900, h1905, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1908 | h1908
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1909 | h1909
                    · linarith only [h1810, h1909, hlam]
                    · linarith only [h1909, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1912 | h1912
                    · linarith only [h1810, h1912, hlam]
                    · linarith only [h1912, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1883, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1916 | h1916
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1917 | h1917
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1918 | h1918
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1919 | h1919
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1920 | h1920
                    · linarith only [h1810, h1920, hlam]
                    · linarith only [h1917, h1920, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1923 | h1923
                    · linarith only [h1810, h1923, hlam]
                    · linarith only [h1917, h1923, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1926 | h1926
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1927 | h1927
                    · linarith only [h1810, h1927, hlam]
                    · linarith only [h1917, h1927, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1930 | h1930
                    · linarith only [h1810, h1930, hlam]
                    · linarith only [h1917, h1930, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1933 | h1933
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1934 | h1934
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1935 | h1935
                    · linarith only [h1810, h1935, hlam]
                    · linarith only [h1935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1938 | h1938
                    · linarith only [h1810, h1938, hlam]
                    · linarith only [h1933, h1938, hc13, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1941 | h1941
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1942 | h1942
                    · linarith only [h1810, h1942, hlam]
                    · linarith only [h1942, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1945 | h1945
                    · linarith only [h1810, h1945, hlam]
                    · linarith only [h1945, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1916, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1949 | h1949
    · linarith only [h1949, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
    · rcases p0_3 (m.d 1 5) (by simp) with h1951 | h1951
      · linarith only [h1951, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi2]
      · rcases p0_3 (m.d 2 5) (by simp) with h1953 | h1953
        · linarith only [h1953, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1955 | h1955
          · rcases p0_3 (m.d 4 5) (by simp) with h1956 | h1956
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1957 | h1957
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1958 | h1958
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1959 | h1959
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1960 | h1960
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h1961 | h1961
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1962 | h1962
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1963 | h1963
                          · linarith only [h1949, h1963, hlam]
                          · linarith only [h1955, h1961, h1963, hc23, hc35, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1966 | h1966
                          · linarith only [h1949, h1966, hlam]
                          · linarith only [h1961, h1966, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h1969 | h1969
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1970 | h1970
                          · linarith only [h1949, h1970, hlam]
                          · linarith only [h1970, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h1973 | h1973
                          · linarith only [h1949, h1973, hlam]
                          · linarith only [h1957, h1973, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1951, h1960, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1977 | h1977
                    · linarith only [h1959, h1977, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h1977, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1980 | h1980
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1981 | h1981
                    · linarith only [h1958, h1981, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1951, h1981, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1984 | h1984
                    · linarith only [h1980, h1984, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h1984, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1987 | h1987
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1988 | h1988
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1989 | h1989
                    · linarith only [h1957, h1989, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1951, h1989, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1992 | h1992
                    · linarith only [h1988, h1992, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h1992, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1995 | h1995
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1996 | h1996
                    · linarith only [h1987, h1996, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1951, h1996, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h1999 | h1999
                    · linarith only [h1995, h1999, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h1999, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1956, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h2003 | h2003
            · rcases m.htr 0 1 2 (by decide) (by decide) with h2004 | h2004
              · rcases m.htr 0 1 3 (by decide) (by decide) with h2005 | h2005
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2006 | h2006
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2007 | h2007
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h2008 | h2008
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h2009 | h2009
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2010 | h2010
                          · linarith only [h1949, h2010, hlam]
                          · linarith only [h2008, h2010, hc23, hc45, hlam, hphi, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2013 | h2013
                          · linarith only [h1949, h2013, hlam]
                          · linarith only [h2008, h2013, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h2016 | h2016
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2017 | h2017
                          · linarith only [h1949, h2017, hlam]
                          · linarith only [h2017, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2020 | h2020
                          · linarith only [h1949, h2020, hlam]
                          · linarith only [h2004, h2020, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1951, h2007, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2024 | h2024
                    · linarith only [h2006, h2024, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h2024, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2027 | h2027
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2028 | h2028
                    · linarith only [h2005, h2028, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1951, h2028, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2031 | h2031
                    · linarith only [h2027, h2031, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h2031, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h2034 | h2034
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2035 | h2035
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2036 | h2036
                    · linarith only [h2004, h2036, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h1951, h2036, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2039 | h2039
                    · linarith only [h2035, h2039, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h2039, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2042 | h2042
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2043 | h2043
                    · linarith only [h2034, h2043, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h1951, h2043, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2046 | h2046
                    · linarith only [h2042, h2046, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h1951, h2046, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2003, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h2050 | h2050
    · linarith only [h2050, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · rcases p0_3 (m.d 1 5) (by simp) with h2052 | h2052
      · linarith only [h2052, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi3]
      · rcases p0_3 (m.d 2 5) (by simp) with h2054 | h2054
        · rcases p0_3 (m.d 3 5) (by simp) with h2055 | h2055
          · linarith only [h2055, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h2057 | h2057
            · rcases m.htr 0 1 2 (by decide) (by decide) with h2058 | h2058
              · rcases m.htr 0 1 3 (by decide) (by decide) with h2059 | h2059
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2060 | h2060
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2061 | h2061
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h2062 | h2062
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h2063 | h2063
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2064 | h2064
                          · linarith only [h2050, h2054, h2058, h2061, h2064, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi1]
                          · linarith only [h2050, h2062, h2064, hc23, hc45, hlam, hphi, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2067 | h2067
                          · linarith only [h2050, h2054, h2067, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · linarith only [h2050, h2062, h2067, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h2070 | h2070
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2071 | h2071
                          · linarith only [h2050, h2054, h2071, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi0]
                          · linarith only [h2050, h2070, h2071, hc24, hc45, hlam, hphi, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2074 | h2074
                          · linarith only [h2050, h2054, h2061, h2074, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi1]
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h2076 | h2076
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2077 | h2077
                              · linarith only [h2050, h2077, hlam]
                              · linarith only [h2054, h2076, h2077, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2080 | h2080
                              · linarith only [h2050, h2080, hlam]
                              · linarith only [h2062, h2080, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h2052, h2061, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2084 | h2084
                    · linarith only [h2060, h2084, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2084, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2087 | h2087
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2088 | h2088
                    · linarith only [h2059, h2088, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h2052, h2088, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2091 | h2091
                    · linarith only [h2087, h2091, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2091, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h2094 | h2094
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2095 | h2095
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2096 | h2096
                    · linarith only [h2058, h2096, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h2052, h2096, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2099 | h2099
                    · linarith only [h2095, h2099, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2099, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2102 | h2102
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2103 | h2103
                    · linarith only [h2094, h2103, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h2052, h2103, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2106 | h2106
                    · linarith only [h2102, h2106, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2106, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2057, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h2110 | h2110
          · linarith only [h2110, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h2112 | h2112
            · rcases m.htr 0 1 2 (by decide) (by decide) with h2113 | h2113
              · rcases m.htr 0 1 3 (by decide) (by decide) with h2114 | h2114
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2115 | h2115
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2116 | h2116
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h2117 | h2117
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h2118 | h2118
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2119 | h2119
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h2120 | h2120
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2121 | h2121
                              · linarith only [h2050, h2121, hlam]
                              · linarith only [h2121, hc03, hc45, hlam, hphi, ht34, p0_1]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2124 | h2124
                              · linarith only [h2050, h2124, hlam]
                              · linarith only [h2114, h2124, hc13, hc45, hlam, hphi, ht34, p0_1]
                          · linarith only [h2054, h2119, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2128 | h2128
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h2129 | h2129
                            · linarith only [h2117, h2118, h2129, hlam]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2131 | h2131
                              · linarith only [h2050, h2131, hlam]
                              · linarith only [h2131, hc03, hc45, hlam, hphi, ht34, p0_1]
                          · linarith only [h2054, h2117, h2128, hc23, hc45, hlam, hphi, ht34, p0_1]
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h2135 | h2135
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2136 | h2136
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h2137 | h2137
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2138 | h2138
                              · linarith only [h2050, h2138, hlam]
                              · linarith only [h2117, h2136, h2138, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                            · linarith only [h2117, h2135, h2137, hlam]
                          · linarith only [h2054, h2136, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h2143 | h2143
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h2144 | h2144
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2145 | h2145
                              · linarith only [h2050, h2145, hlam]
                              · linarith only [h2135, h2143, h2144, h2145, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u5ehi2]
                            · rcases m.htr 0 3 5 (by decide) (by decide) with h2148 | h2148
                              · linarith only [h2050, h2148, hlam]
                              · linarith only [h2148, hc03, hc45, hlam, hphi, ht34, p0_1]
                          · linarith only [h2054, h2143, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h2052, h2116, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2153 | h2153
                    · linarith only [h2115, h2153, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2153, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2156 | h2156
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2157 | h2157
                    · linarith only [h2114, h2157, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h2052, h2157, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2160 | h2160
                    · linarith only [h2156, h2160, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2160, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h2163 | h2163
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2164 | h2164
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2165 | h2165
                    · linarith only [h2113, h2165, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
                    · linarith only [h2052, h2165, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2168 | h2168
                    · linarith only [h2164, h2168, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2168, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h2171 | h2171
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2172 | h2172
                    · linarith only [h2163, h2172, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
                    · linarith only [h2052, h2172, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h2175 | h2175
                    · linarith only [h2171, h2175, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
                    · linarith only [h2052, h2175, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h2112, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

set_option maxHeartbeats 4912000 in
theorem n7l_sBT1_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
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
            · rcases h5bigk with h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hlam, p9_0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [h7, hc15, hlam, hphi, ht0b, ht5b, p0_1, p9_1, u0elo0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [h7, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p9_1, u1elo0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [h7, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p9_1, u1elo0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [h7, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p9_1, u1elo0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc05, hlam, hphi, p9_1, u5elo1]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hlam, p9_0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc25, hlam, hphi, p9_1, u5elo1]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc35, hlam, hphi, p9_1, u5elo1]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc45, hlam, hphi, p9_1, u5elo1]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc05, hlam, hphi, p9_1, u5elo2]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc15, hlam, hphi, p9_1, u5elo2]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hlam, p9_0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc35, hlam, hphi, p9_1, u5elo2]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc45, hlam, hphi, p9_1, u5elo2]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc05, hlam, hphi, p9_1, u5elo3]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc15, hlam, hphi, p9_1, u5elo3]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc25, hlam, hphi, p9_1, u5elo3]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hlam, p9_0]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc45, hlam, hphi, p9_1, u5elo3]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc05, hlam, hphi, p9_1, u5elo4]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc15, hlam, hphi, p9_1, u5elo4]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc25, hlam, hphi, p9_1, u5elo4]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hc35, hlam, hphi, p9_1, u5elo4]
              · have p9_0 := h9c.1
                have p9_1 := h9c.2.1
                have p9_2 := h9c.2.2.1
                have p9_3 := h9c.2.2.2
                linarith only [hlam, p9_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h35 | h35
            · linarith only [h35, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hlam, p37_0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [h35, hc15, hlam, hphi, ht0b, ht5b, p0_1, p37_1, u0elo0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [h35, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p37_1, u1elo0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [h35, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p37_1, u1elo0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [h35, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p37_1, u1elo0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc05, hlam, hphi, p37_1, u5elo1]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hlam, p37_0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc25, hlam, hphi, p37_1, u5elo1]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc35, hlam, hphi, p37_1, u5elo1]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc45, hlam, hphi, p37_1, u5elo1]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc05, hlam, hphi, p37_1, u5elo2]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc15, hlam, hphi, p37_1, u5elo2]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hlam, p37_0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc35, hlam, hphi, p37_1, u5elo2]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc45, hlam, hphi, p37_1, u5elo2]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc05, hlam, hphi, p37_1, u5elo3]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc15, hlam, hphi, p37_1, u5elo3]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc25, hlam, hphi, p37_1, u5elo3]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hlam, p37_0]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc45, hlam, hphi, p37_1, u5elo3]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc05, hlam, hphi, p37_1, u5elo4]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc15, hlam, hphi, p37_1, u5elo4]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc25, hlam, hphi, p37_1, u5elo4]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hc35, hlam, hphi, p37_1, u5elo4]
              · have p37_0 := h37c.1
                have p37_1 := h37c.2.1
                have p37_2 := h37c.2.2.1
                have p37_3 := h37c.2.2.2
                linarith only [hlam, p37_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h63 | h63
          · rcases p0_3 (m.d 0 5) (by simp) with h64 | h64
            · linarith only [h64, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h64, hc15, hlam, hphi, ht0b, ht5b, p0_1, p66_1, u0elo0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h64, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p66_1, u1elo0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h64, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p66_1, u1elo0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [h64, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p66_1, u1elo0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc05, hlam, hphi, p66_1, u5elo1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc25, hlam, hphi, p66_1, u5elo1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc35, hlam, hphi, p66_1, u5elo1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc45, hlam, hphi, p66_1, u5elo1]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc05, hlam, hphi, p66_1, u5elo2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc15, hlam, hphi, p66_1, u5elo2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc35, hlam, hphi, p66_1, u5elo2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc45, hlam, hphi, p66_1, u5elo2]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc05, hlam, hphi, p66_1, u5elo3]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc15, hlam, hphi, p66_1, u5elo3]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc25, hlam, hphi, p66_1, u5elo3]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc45, hlam, hphi, p66_1, u5elo3]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc05, hlam, hphi, p66_1, u5elo4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc15, hlam, hphi, p66_1, u5elo4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc25, hlam, hphi, p66_1, u5elo4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hc35, hlam, hphi, p66_1, u5elo4]
              · have p66_0 := h66c.1
                have p66_1 := h66c.2.1
                have p66_2 := h66c.2.2.1
                have p66_3 := h66c.2.2.2
                linarith only [hlam, p66_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h92 | h92
            · linarith only [h92, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
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
                linarith only [h92, hc15, hlam, hphi, ht0b, ht5b, p0_1, p94_1, u0elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h92, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h92, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [h92, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p94_1, u1elo0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc05, hlam, hphi, p94_1, u5elo1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc25, hlam, hphi, p94_1, u5elo1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc35, hlam, hphi, p94_1, u5elo1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc45, hlam, hphi, p94_1, u5elo1]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc05, hlam, hphi, p94_1, u5elo2]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc15, hlam, hphi, p94_1, u5elo2]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc35, hlam, hphi, p94_1, u5elo2]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc45, hlam, hphi, p94_1, u5elo2]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc05, hlam, hphi, p94_1, u5elo3]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc15, hlam, hphi, p94_1, u5elo3]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc25, hlam, hphi, p94_1, u5elo3]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc45, hlam, hphi, p94_1, u5elo3]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc05, hlam, hphi, p94_1, u5elo4]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc15, hlam, hphi, p94_1, u5elo4]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc25, hlam, hphi, p94_1, u5elo4]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hc35, hlam, hphi, p94_1, u5elo4]
              · have p94_0 := h94c.1
                have p94_1 := h94c.2.1
                have p94_2 := h94c.2.2.1
                have p94_3 := h94c.2.2.2
                linarith only [hlam, p94_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h121 | h121
    · rcases p0_3 (m.d 0 2) (by simp) with h122 | h122
      · rcases p0_3 (m.d 0 3) (by simp) with h123 | h123
        · linarith only [h123, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h125 | h125
          · rcases p0_3 (m.d 0 5) (by simp) with h126 | h126
            · linarith only [h126, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h126, hc15, hlam, hphi, ht0b, ht5b, p0_1, p128_1, u0elo0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h126, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p128_1, u1elo0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h126, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p128_1, u1elo0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [h126, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p128_1, u1elo0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc05, hlam, hphi, p128_1, u5elo1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc25, hlam, hphi, p128_1, u5elo1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc35, hlam, hphi, p128_1, u5elo1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc45, hlam, hphi, p128_1, u5elo1]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc05, hlam, hphi, p128_1, u5elo2]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc15, hlam, hphi, p128_1, u5elo2]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc35, hlam, hphi, p128_1, u5elo2]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc45, hlam, hphi, p128_1, u5elo2]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc05, hlam, hphi, p128_1, u5elo3]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc15, hlam, hphi, p128_1, u5elo3]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc25, hlam, hphi, p128_1, u5elo3]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc45, hlam, hphi, p128_1, u5elo3]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc05, hlam, hphi, p128_1, u5elo4]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc15, hlam, hphi, p128_1, u5elo4]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc25, hlam, hphi, p128_1, u5elo4]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hc35, hlam, hphi, p128_1, u5elo4]
              · have p128_0 := h128c.1
                have p128_1 := h128c.2.1
                have p128_2 := h128c.2.2.1
                have p128_3 := h128c.2.2.2
                linarith only [hlam, p128_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h154 | h154
            · linarith only [h154, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
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
                linarith only [h154, hc15, hlam, hphi, ht0b, ht5b, p0_1, p156_1, u0elo0]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [h154, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p156_1, u1elo0]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [h154, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p156_1, u1elo0]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [h154, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p156_1, u1elo0]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc05, hlam, hphi, p156_1, u5elo1]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hlam, p156_0]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc25, hlam, hphi, p156_1, u5elo1]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc35, hlam, hphi, p156_1, u5elo1]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc45, hlam, hphi, p156_1, u5elo1]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc05, hlam, hphi, p156_1, u5elo2]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc15, hlam, hphi, p156_1, u5elo2]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hlam, p156_0]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc35, hlam, hphi, p156_1, u5elo2]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc45, hlam, hphi, p156_1, u5elo2]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc05, hlam, hphi, p156_1, u5elo3]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc15, hlam, hphi, p156_1, u5elo3]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc25, hlam, hphi, p156_1, u5elo3]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hlam, p156_0]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc45, hlam, hphi, p156_1, u5elo3]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc05, hlam, hphi, p156_1, u5elo4]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc15, hlam, hphi, p156_1, u5elo4]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc25, hlam, hphi, p156_1, u5elo4]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hc35, hlam, hphi, p156_1, u5elo4]
              · have p156_0 := h156c.1
                have p156_1 := h156c.2.1
                have p156_2 := h156c.2.2.1
                have p156_3 := h156c.2.2.2
                linarith only [hlam, p156_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h182 | h182
        · linarith only [h182, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
          · rcases p0_3 (m.d 0 5) (by simp) with h185 | h185
            · linarith only [h122, h185, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
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
                linarith only [h185, hc15, hlam, hphi, ht0b, ht5b, p0_1, p187_1, u0elo0]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [h185, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p187_1, u1elo0]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [h185, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p187_1, u1elo0]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [h185, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p187_1, u1elo0]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc05, hlam, hphi, p187_1, u5elo1]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hlam, p187_0]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc25, hlam, hphi, p187_1, u5elo1]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc35, hlam, hphi, p187_1, u5elo1]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc45, hlam, hphi, p187_1, u5elo1]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc05, hlam, hphi, p187_1, u5elo2]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc15, hlam, hphi, p187_1, u5elo2]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hlam, p187_0]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc35, hlam, hphi, p187_1, u5elo2]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc45, hlam, hphi, p187_1, u5elo2]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc05, hlam, hphi, p187_1, u5elo3]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc15, hlam, hphi, p187_1, u5elo3]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc25, hlam, hphi, p187_1, u5elo3]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hlam, p187_0]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc45, hlam, hphi, p187_1, u5elo3]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc05, hlam, hphi, p187_1, u5elo4]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc15, hlam, hphi, p187_1, u5elo4]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc25, hlam, hphi, p187_1, u5elo4]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hc35, hlam, hphi, p187_1, u5elo4]
              · have p187_0 := h187c.1
                have p187_1 := h187c.2.1
                have p187_2 := h187c.2.2.1
                have p187_3 := h187c.2.2.2
                linarith only [hlam, p187_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h213 | h213
            · linarith only [h122, h213, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c | h215c
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hlam, p215_0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [h213, hc15, hlam, hphi, ht0b, ht5b, p0_1, p215_1, u0elo0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [h213, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p215_1, u1elo0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [h213, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p215_1, u1elo0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [h213, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p215_1, u1elo0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc05, hlam, hphi, p215_1, u5elo1]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hlam, p215_0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc25, hlam, hphi, p215_1, u5elo1]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc35, hlam, hphi, p215_1, u5elo1]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc45, hlam, hphi, p215_1, u5elo1]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc05, hlam, hphi, p215_1, u5elo2]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc15, hlam, hphi, p215_1, u5elo2]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hlam, p215_0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc35, hlam, hphi, p215_1, u5elo2]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc45, hlam, hphi, p215_1, u5elo2]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc05, hlam, hphi, p215_1, u5elo3]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc15, hlam, hphi, p215_1, u5elo3]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc25, hlam, hphi, p215_1, u5elo3]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hlam, p215_0]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc45, hlam, hphi, p215_1, u5elo3]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc05, hlam, hphi, p215_1, u5elo4]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc15, hlam, hphi, p215_1, u5elo4]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc25, hlam, hphi, p215_1, u5elo4]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hc35, hlam, hphi, p215_1, u5elo4]
              · have p215_0 := h215c.1
                have p215_1 := h215c.2.1
                have p215_2 := h215c.2.2.1
                have p215_3 := h215c.2.2.2
                linarith only [hlam, p215_0]
    · linarith only [h121, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h242 | h242
    · rcases p0_3 (m.d 0 2) (by simp) with h243 | h243
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · linarith only [h245, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h247 | h247
            · linarith only [h247, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · rcases h5bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hlam, p249_0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [h247, hc15, hlam, hphi, ht0b, ht5b, p0_1, p249_1, u0elo0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [h247, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p249_1, u1elo0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [h247, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p249_1, u1elo0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [h247, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p249_1, u1elo0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc05, hlam, hphi, p249_1, u5elo1]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hlam, p249_0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc25, hlam, hphi, p249_1, u5elo1]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc35, hlam, hphi, p249_1, u5elo1]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc45, hlam, hphi, p249_1, u5elo1]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc05, hlam, hphi, p249_1, u5elo2]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc15, hlam, hphi, p249_1, u5elo2]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hlam, p249_0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc35, hlam, hphi, p249_1, u5elo2]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc45, hlam, hphi, p249_1, u5elo2]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc05, hlam, hphi, p249_1, u5elo3]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc15, hlam, hphi, p249_1, u5elo3]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc25, hlam, hphi, p249_1, u5elo3]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hlam, p249_0]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc45, hlam, hphi, p249_1, u5elo3]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc05, hlam, hphi, p249_1, u5elo4]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc15, hlam, hphi, p249_1, u5elo4]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc25, hlam, hphi, p249_1, u5elo4]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hc35, hlam, hphi, p249_1, u5elo4]
              · have p249_0 := h249c.1
                have p249_1 := h249c.2.1
                have p249_2 := h249c.2.2.1
                have p249_3 := h249c.2.2.2
                linarith only [hlam, p249_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h275 | h275
          · linarith only [h275, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h277 | h277
            · linarith only [h244, h277, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hlam, p279_0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [h277, hc15, hlam, hphi, ht0b, ht5b, p0_1, p279_1, u0elo0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [h277, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p279_1, u1elo0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [h277, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p279_1, u1elo0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [h277, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p279_1, u1elo0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc05, hlam, hphi, p279_1, u5elo1]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hlam, p279_0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc25, hlam, hphi, p279_1, u5elo1]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc35, hlam, hphi, p279_1, u5elo1]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc45, hlam, hphi, p279_1, u5elo1]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc05, hlam, hphi, p279_1, u5elo2]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc15, hlam, hphi, p279_1, u5elo2]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hlam, p279_0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc35, hlam, hphi, p279_1, u5elo2]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc45, hlam, hphi, p279_1, u5elo2]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc05, hlam, hphi, p279_1, u5elo3]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc15, hlam, hphi, p279_1, u5elo3]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc25, hlam, hphi, p279_1, u5elo3]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hlam, p279_0]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc45, hlam, hphi, p279_1, u5elo3]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc05, hlam, hphi, p279_1, u5elo4]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc15, hlam, hphi, p279_1, u5elo4]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc25, hlam, hphi, p279_1, u5elo4]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hc35, hlam, hphi, p279_1, u5elo4]
              · have p279_0 := h279c.1
                have p279_1 := h279c.2.1
                have p279_2 := h279c.2.2.1
                have p279_3 := h279c.2.2.2
                linarith only [hlam, p279_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h305 | h305
        · rcases p0_3 (m.d 0 4) (by simp) with h306 | h306
          · linarith only [h306, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · linarith only [h243, h308, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h308, hc15, hlam, hphi, ht0b, ht5b, p0_1, p310_1, u0elo0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h308, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p310_1, u1elo0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h308, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p310_1, u1elo0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [h308, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p310_1, u1elo0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc05, hlam, hphi, p310_1, u5elo1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc25, hlam, hphi, p310_1, u5elo1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc35, hlam, hphi, p310_1, u5elo1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc45, hlam, hphi, p310_1, u5elo1]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc05, hlam, hphi, p310_1, u5elo2]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc15, hlam, hphi, p310_1, u5elo2]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc35, hlam, hphi, p310_1, u5elo2]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc45, hlam, hphi, p310_1, u5elo2]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc05, hlam, hphi, p310_1, u5elo3]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc15, hlam, hphi, p310_1, u5elo3]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc25, hlam, hphi, p310_1, u5elo3]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc45, hlam, hphi, p310_1, u5elo3]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc05, hlam, hphi, p310_1, u5elo4]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc15, hlam, hphi, p310_1, u5elo4]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc25, hlam, hphi, p310_1, u5elo4]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hc35, hlam, hphi, p310_1, u5elo4]
              · have p310_0 := h310c.1
                have p310_1 := h310c.2.1
                have p310_2 := h310c.2.2.1
                have p310_3 := h310c.2.2.2
                linarith only [hlam, p310_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h336 | h336
          · linarith only [h336, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h338 | h338
            · linarith only [h305, h338, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h338, hc15, hlam, hphi, ht0b, ht5b, p0_1, p340_1, u0elo0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h338, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p340_1, u1elo0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h338, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p340_1, u1elo0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [h338, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p340_1, u1elo0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc05, hlam, hphi, p340_1, u5elo1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc25, hlam, hphi, p340_1, u5elo1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc35, hlam, hphi, p340_1, u5elo1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc45, hlam, hphi, p340_1, u5elo1]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc05, hlam, hphi, p340_1, u5elo2]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc15, hlam, hphi, p340_1, u5elo2]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc35, hlam, hphi, p340_1, u5elo2]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc45, hlam, hphi, p340_1, u5elo2]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc05, hlam, hphi, p340_1, u5elo3]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc15, hlam, hphi, p340_1, u5elo3]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc25, hlam, hphi, p340_1, u5elo3]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc45, hlam, hphi, p340_1, u5elo3]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc05, hlam, hphi, p340_1, u5elo4]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc15, hlam, hphi, p340_1, u5elo4]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc25, hlam, hphi, p340_1, u5elo4]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hc35, hlam, hphi, p340_1, u5elo4]
              · have p340_0 := h340c.1
                have p340_1 := h340c.2.1
                have p340_2 := h340c.2.2.1
                have p340_3 := h340c.2.2.2
                linarith only [hlam, p340_0]
    · linarith only [h242, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h367 | h367
    · rcases p0_3 (m.d 0 2) (by simp) with h368 | h368
      · rcases p0_3 (m.d 0 3) (by simp) with h369 | h369
        · rcases p0_3 (m.d 0 4) (by simp) with h370 | h370
          · rcases p0_3 (m.d 0 5) (by simp) with h371 | h371
            · linarith only [h371, hlam, p0_0]
            · rcases h5bigk with h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc15, hlam, hphi, p373_1, u5elo0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p373_1, u1elo0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p373_1, u1elo0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p373_1, u1elo0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc05, hlam, hphi, p373_1, u5elo1]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc25, hlam, hphi, p373_1, u5elo1]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc35, hlam, hphi, p373_1, u5elo1]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc45, hlam, hphi, p373_1, u5elo1]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc05, hlam, hphi, p373_1, u5elo2]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc15, hlam, hphi, p373_1, u5elo2]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc35, hlam, hphi, p373_1, u5elo2]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc45, hlam, hphi, p373_1, u5elo2]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc05, hlam, hphi, p373_1, u5elo3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc15, hlam, hphi, p373_1, u5elo3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc25, hlam, hphi, p373_1, u5elo3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc45, hlam, hphi, p373_1, u5elo3]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc05, hlam, hphi, p373_1, u5elo4]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc15, hlam, hphi, p373_1, u5elo4]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc25, hlam, hphi, p373_1, u5elo4]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hc35, hlam, hphi, p373_1, u5elo4]
              · have p373_0 := h373c.1
                have p373_1 := h373c.2.1
                have p373_2 := h373c.2.2.1
                have p373_3 := h373c.2.2.2
                linarith only [hlam, p373_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h399 | h399
            · linarith only [h399, hlam, p0_0]
            · rcases h5bigk with h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hlam, p401_0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc15, hlam, hphi, p401_1, u5elo0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p401_1, u1elo0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p401_1, u1elo0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p401_1, u1elo0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc05, hlam, hphi, p401_1, u5elo1]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hlam, p401_0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc25, hlam, hphi, p401_1, u5elo1]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc35, hlam, hphi, p401_1, u5elo1]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc45, hlam, hphi, p401_1, u5elo1]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [h370, hc04, hlam, hphi, ht45, p401_1, u5elo2]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc15, hlam, hphi, p401_1, u5elo2]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hlam, p401_0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc35, hlam, hphi, p401_1, u5elo2]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc45, hlam, hphi, p401_1, u5elo2]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [h370, hc04, hlam, hphi, ht45, p401_1, u5elo3]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc15, hlam, hphi, p401_1, u5elo3]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc25, hlam, hphi, p401_1, u5elo3]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hlam, p401_0]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc45, hlam, hphi, p401_1, u5elo3]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [h370, hc04, hlam, hphi, ht45, p401_1, u5elo4]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc15, hlam, hphi, p401_1, u5elo4]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc25, hlam, hphi, p401_1, u5elo4]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hc35, hlam, hphi, p401_1, u5elo4]
              · have p401_0 := h401c.1
                have p401_1 := h401c.2.1
                have p401_2 := h401c.2.2.1
                have p401_3 := h401c.2.2.2
                linarith only [hlam, p401_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h427 | h427
          · rcases p0_3 (m.d 0 5) (by simp) with h428 | h428
            · linarith only [h428, hlam, p0_0]
            · rcases h5bigk with h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hlam, p430_0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc15, hlam, hphi, p430_1, u5elo0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p430_1, u1elo0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p430_1, u1elo0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p430_1, u1elo0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc05, hlam, hphi, p430_1, u5elo1]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hlam, p430_0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc25, hlam, hphi, p430_1, u5elo1]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc35, hlam, hphi, p430_1, u5elo1]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc45, hlam, hphi, p430_1, u5elo1]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [h369, hc03, hlam, hphi, ht34, ht45, p430_1, u5elo2]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc15, hlam, hphi, p430_1, u5elo2]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hlam, p430_0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc35, hlam, hphi, p430_1, u5elo2]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc45, hlam, hphi, p430_1, u5elo2]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [h369, hc03, hlam, hphi, ht34, ht45, p430_1, u5elo3]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc15, hlam, hphi, p430_1, u5elo3]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc25, hlam, hphi, p430_1, u5elo3]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hlam, p430_0]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc45, hlam, hphi, p430_1, u5elo3]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [h369, hc03, hlam, hphi, ht34, ht45, p430_1, u5elo4]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc15, hlam, hphi, p430_1, u5elo4]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc25, hlam, hphi, p430_1, u5elo4]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hc35, hlam, hphi, p430_1, u5elo4]
              · have p430_0 := h430c.1
                have p430_1 := h430c.2.1
                have p430_2 := h430c.2.2.1
                have p430_3 := h430c.2.2.2
                linarith only [hlam, p430_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h456 | h456
            · linarith only [h456, hlam, p0_0]
            · rcases h5bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hlam, p458_0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc15, hlam, hphi, p458_1, u5elo0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p458_1, u1elo0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p458_1, u1elo0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p458_1, u1elo0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [h427, hc04, hlam, hphi, ht45, p458_1, u5elo1]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hlam, p458_0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc25, hlam, hphi, p458_1, u5elo1]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc35, hlam, hphi, p458_1, u5elo1]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc45, hlam, hphi, p458_1, u5elo1]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [h369, hc03, hlam, hphi, ht34, ht45, p458_1, u5elo2]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc15, hlam, hphi, p458_1, u5elo2]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hlam, p458_0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc35, hlam, hphi, p458_1, u5elo2]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc45, hlam, hphi, p458_1, u5elo2]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [h369, hc03, hlam, hphi, ht34, ht45, p458_1, u5elo3]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc15, hlam, hphi, p458_1, u5elo3]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc25, hlam, hphi, p458_1, u5elo3]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hlam, p458_0]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc45, hlam, hphi, p458_1, u5elo3]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [h369, hc03, hlam, hphi, ht34, ht45, p458_1, u5elo4]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc15, hlam, hphi, p458_1, u5elo4]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc25, hlam, hphi, p458_1, u5elo4]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hc35, hlam, hphi, p458_1, u5elo4]
              · have p458_0 := h458c.1
                have p458_1 := h458c.2.1
                have p458_2 := h458c.2.2.1
                have p458_3 := h458c.2.2.2
                linarith only [hlam, p458_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h484 | h484
        · rcases p0_3 (m.d 0 4) (by simp) with h485 | h485
          · rcases p0_3 (m.d 0 5) (by simp) with h486 | h486
            · linarith only [h486, hlam, p0_0]
            · rcases h5bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hlam, p488_0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc15, hlam, hphi, p488_1, u5elo0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p488_1, u1elo0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p488_1, u1elo0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p488_1, u1elo0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc05, hlam, hphi, p488_1, u5elo1]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hlam, p488_0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc25, hlam, hphi, p488_1, u5elo1]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc35, hlam, hphi, p488_1, u5elo1]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc45, hlam, hphi, p488_1, u5elo1]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p488_1, u5elo2]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc15, hlam, hphi, p488_1, u5elo2]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hlam, p488_0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc35, hlam, hphi, p488_1, u5elo2]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc45, hlam, hphi, p488_1, u5elo2]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p488_1, u5elo3]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc15, hlam, hphi, p488_1, u5elo3]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc25, hlam, hphi, p488_1, u5elo3]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hlam, p488_0]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc45, hlam, hphi, p488_1, u5elo3]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p488_1, u5elo4]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc15, hlam, hphi, p488_1, u5elo4]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc25, hlam, hphi, p488_1, u5elo4]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hc35, hlam, hphi, p488_1, u5elo4]
              · have p488_0 := h488c.1
                have p488_1 := h488c.2.1
                have p488_2 := h488c.2.2.1
                have p488_3 := h488c.2.2.2
                linarith only [hlam, p488_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h514 | h514
            · linarith only [h514, hlam, p0_0]
            · rcases h5bigk with h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hlam, p516_0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc15, hlam, hphi, p516_1, u5elo0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p516_1, u1elo0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p516_1, u1elo0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p516_1, u1elo0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [h485, hc04, hlam, hphi, ht45, p516_1, u5elo1]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hlam, p516_0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc25, hlam, hphi, p516_1, u5elo1]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc35, hlam, hphi, p516_1, u5elo1]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc45, hlam, hphi, p516_1, u5elo1]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p516_1, u5elo2]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc15, hlam, hphi, p516_1, u5elo2]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hlam, p516_0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc35, hlam, hphi, p516_1, u5elo2]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc45, hlam, hphi, p516_1, u5elo2]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p516_1, u5elo3]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc15, hlam, hphi, p516_1, u5elo3]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc25, hlam, hphi, p516_1, u5elo3]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hlam, p516_0]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc45, hlam, hphi, p516_1, u5elo3]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p516_1, u5elo4]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc15, hlam, hphi, p516_1, u5elo4]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc25, hlam, hphi, p516_1, u5elo4]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hc35, hlam, hphi, p516_1, u5elo4]
              · have p516_0 := h516c.1
                have p516_1 := h516c.2.1
                have p516_2 := h516c.2.2.1
                have p516_3 := h516c.2.2.2
                linarith only [hlam, p516_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h542 | h542
          · rcases p0_3 (m.d 0 5) (by simp) with h543 | h543
            · linarith only [h543, hlam, p0_0]
            · rcases h5bigk with h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hlam, p545_0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc15, hlam, hphi, p545_1, u5elo0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p545_1, u1elo0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p545_1, u1elo0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p545_1, u1elo0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [h484, hc03, hlam, hphi, ht34, ht45, p545_1, u5elo1]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hlam, p545_0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc25, hlam, hphi, p545_1, u5elo1]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc35, hlam, hphi, p545_1, u5elo1]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc45, hlam, hphi, p545_1, u5elo1]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p545_1, u5elo2]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc15, hlam, hphi, p545_1, u5elo2]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hlam, p545_0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc35, hlam, hphi, p545_1, u5elo2]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc45, hlam, hphi, p545_1, u5elo2]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p545_1, u5elo3]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc15, hlam, hphi, p545_1, u5elo3]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc25, hlam, hphi, p545_1, u5elo3]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hlam, p545_0]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc45, hlam, hphi, p545_1, u5elo3]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p545_1, u5elo4]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc15, hlam, hphi, p545_1, u5elo4]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc25, hlam, hphi, p545_1, u5elo4]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hc35, hlam, hphi, p545_1, u5elo4]
              · have p545_0 := h545c.1
                have p545_1 := h545c.2.1
                have p545_2 := h545c.2.2.1
                have p545_3 := h545c.2.2.2
                linarith only [hlam, p545_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h571 | h571
            · linarith only [h571, hlam, p0_0]
            · rcases h5bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc15, hlam, hphi, p573_1, u5elo0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p573_1, u1elo0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p573_1, u1elo0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p573_1, u1elo0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h542, hc04, hlam, hphi, ht45, p573_1, u5elo1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc25, hlam, hphi, p573_1, u5elo1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc35, hlam, hphi, p573_1, u5elo1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc45, hlam, hphi, p573_1, u5elo1]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p573_1, u5elo2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc15, hlam, hphi, p573_1, u5elo2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc35, hlam, hphi, p573_1, u5elo2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc45, hlam, hphi, p573_1, u5elo2]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p573_1, u5elo3]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc15, hlam, hphi, p573_1, u5elo3]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc25, hlam, hphi, p573_1, u5elo3]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc45, hlam, hphi, p573_1, u5elo3]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [h368, hc02, hlam, hphi, ht23, ht34, ht45, p573_1, u5elo4]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc15, hlam, hphi, p573_1, u5elo4]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc25, hlam, hphi, p573_1, u5elo4]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hc35, hlam, hphi, p573_1, u5elo4]
              · have p573_0 := h573c.1
                have p573_1 := h573c.2.1
                have p573_2 := h573c.2.2.1
                have p573_3 := h573c.2.2.2
                linarith only [hlam, p573_0]
    · linarith only [h367, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h600 | h600
    · linarith only [h600, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h602 | h602
      · rcases p0_3 (m.d 0 3) (by simp) with h603 | h603
        · rcases p0_3 (m.d 0 4) (by simp) with h604 | h604
          · rcases p0_3 (m.d 0 5) (by simp) with h605 | h605
            · linarith only [h605, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hlam, p607_0]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [h605, hc15, hlam, hphi, ht0b, ht5b, p0_1, p607_1, u0elo1]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [h604, h605, hc25, hlam, hphi, ht0b, ht5b, p0_1, p607_1, u0elo3]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [h604, h605, hc35, hlam, hphi, ht0b, ht5b, p0_1, p607_1, u0elo3]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [h604, h605, hc45, hlam, hphi, ht0b, ht5b, p0_1, p607_1, u0elo3]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc05, hlam, hphi, p607_1, u5elo1]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hlam, p607_0]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc25, hlam, hphi, p607_1, u5elo1]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc35, hlam, hphi, p607_1, u5elo1]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc45, hlam, hphi, p607_1, u5elo1]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc05, hlam, hphi, p607_1, u5elo2]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc15, hlam, hphi, p607_1, u5elo2]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hlam, p607_0]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc35, hlam, hphi, p607_1, u5elo2]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc45, hlam, hphi, p607_1, u5elo2]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc05, hlam, hphi, p607_1, u5elo3]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc15, hlam, hphi, p607_1, u5elo3]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc25, hlam, hphi, p607_1, u5elo3]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hlam, p607_0]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc45, hlam, hphi, p607_1, u5elo3]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc05, hlam, hphi, p607_1, u5elo4]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc15, hlam, hphi, p607_1, u5elo4]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc25, hlam, hphi, p607_1, u5elo4]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hc35, hlam, hphi, p607_1, u5elo4]
              · have p607_0 := h607c.1
                have p607_1 := h607c.2.1
                have p607_2 := h607c.2.2.1
                have p607_3 := h607c.2.2.2
                linarith only [hlam, p607_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h633 | h633
            · linarith only [h633, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hlam, p635_0]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [h633, hc15, hlam, hphi, ht0b, ht5b, p0_1, p635_1, u0elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [h633, hc25, hlam, hphi, ht0b, ht5b, p0_1, p635_1, u0elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [h633, hc35, hlam, hphi, ht0b, ht5b, p0_1, p635_1, u0elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [h633, hc45, hlam, hphi, ht0b, ht5b, p0_1, p635_1, u0elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc05, hlam, hphi, p635_1, u5elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hlam, p635_0]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc25, hlam, hphi, p635_1, u5elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc35, hlam, hphi, p635_1, u5elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc45, hlam, hphi, p635_1, u5elo1]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc05, hlam, hphi, p635_1, u5elo2]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc15, hlam, hphi, p635_1, u5elo2]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hlam, p635_0]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc35, hlam, hphi, p635_1, u5elo2]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc45, hlam, hphi, p635_1, u5elo2]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc05, hlam, hphi, p635_1, u5elo3]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc15, hlam, hphi, p635_1, u5elo3]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc25, hlam, hphi, p635_1, u5elo3]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hlam, p635_0]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc45, hlam, hphi, p635_1, u5elo3]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc05, hlam, hphi, p635_1, u5elo4]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc15, hlam, hphi, p635_1, u5elo4]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc25, hlam, hphi, p635_1, u5elo4]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hc35, hlam, hphi, p635_1, u5elo4]
              · have p635_0 := h635c.1
                have p635_1 := h635c.2.1
                have p635_2 := h635c.2.2.1
                have p635_3 := h635c.2.2.2
                linarith only [hlam, p635_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h661 | h661
          · rcases p0_3 (m.d 0 5) (by simp) with h662 | h662
            · linarith only [h662, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hlam, p664_0]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [h662, hc15, hlam, hphi, ht0b, ht5b, p0_1, p664_1, u0elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [h662, hc25, hlam, hphi, ht0b, ht5b, p0_1, p664_1, u0elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [h662, hc35, hlam, hphi, ht0b, ht5b, p0_1, p664_1, u0elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [h662, hc45, hlam, hphi, ht0b, ht5b, p0_1, p664_1, u0elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc05, hlam, hphi, p664_1, u5elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hlam, p664_0]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc25, hlam, hphi, p664_1, u5elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc35, hlam, hphi, p664_1, u5elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc45, hlam, hphi, p664_1, u5elo1]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc05, hlam, hphi, p664_1, u5elo2]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc15, hlam, hphi, p664_1, u5elo2]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hlam, p664_0]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc35, hlam, hphi, p664_1, u5elo2]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc45, hlam, hphi, p664_1, u5elo2]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc05, hlam, hphi, p664_1, u5elo3]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc15, hlam, hphi, p664_1, u5elo3]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc25, hlam, hphi, p664_1, u5elo3]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hlam, p664_0]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc45, hlam, hphi, p664_1, u5elo3]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc05, hlam, hphi, p664_1, u5elo4]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc15, hlam, hphi, p664_1, u5elo4]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc25, hlam, hphi, p664_1, u5elo4]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hc35, hlam, hphi, p664_1, u5elo4]
              · have p664_0 := h664c.1
                have p664_1 := h664c.2.1
                have p664_2 := h664c.2.2.1
                have p664_3 := h664c.2.2.2
                linarith only [hlam, p664_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h690 | h690
            · linarith only [h690, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h690, hc15, hlam, hphi, ht0b, ht5b, p0_1, p692_1, u0elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h690, hc25, hlam, hphi, ht0b, ht5b, p0_1, p692_1, u0elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h690, hc35, hlam, hphi, ht0b, ht5b, p0_1, p692_1, u0elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h690, hc45, hlam, hphi, ht0b, ht5b, p0_1, p692_1, u0elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc05, hlam, hphi, p692_1, u5elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc25, hlam, hphi, p692_1, u5elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc35, hlam, hphi, p692_1, u5elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc45, hlam, hphi, p692_1, u5elo1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc05, hlam, hphi, p692_1, u5elo2]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc15, hlam, hphi, p692_1, u5elo2]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc35, hlam, hphi, p692_1, u5elo2]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc45, hlam, hphi, p692_1, u5elo2]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc05, hlam, hphi, p692_1, u5elo3]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc15, hlam, hphi, p692_1, u5elo3]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc25, hlam, hphi, p692_1, u5elo3]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc45, hlam, hphi, p692_1, u5elo3]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc05, hlam, hphi, p692_1, u5elo4]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc15, hlam, hphi, p692_1, u5elo4]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc25, hlam, hphi, p692_1, u5elo4]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hc35, hlam, hphi, p692_1, u5elo4]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
      · linarith only [h602, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h720 | h720
    · rcases p0_3 (m.d 0 2) (by simp) with h721 | h721
      · rcases p0_3 (m.d 0 3) (by simp) with h722 | h722
        · linarith only [h722, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h724 | h724
          · rcases p0_3 (m.d 0 5) (by simp) with h725 | h725
            · linarith only [h725, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hlam, p727_0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [h720, h725, hc15, hlam, hphi, ht0b, ht5b, p0_1, p727_1, u0elo0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [h720, h725, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p727_1, u1elo0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [h720, h725, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p727_1, u1elo0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [h720, h725, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p727_1, u1elo0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc05, hlam, hphi, p727_1, u5elo1]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hlam, p727_0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc25, hlam, hphi, p727_1, u5elo1]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc35, hlam, hphi, p727_1, u5elo1]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc45, hlam, hphi, p727_1, u5elo1]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc05, hlam, hphi, p727_1, u5elo2]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc15, hlam, hphi, p727_1, u5elo2]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hlam, p727_0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc35, hlam, hphi, p727_1, u5elo2]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc45, hlam, hphi, p727_1, u5elo2]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc05, hlam, hphi, p727_1, u5elo3]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc15, hlam, hphi, p727_1, u5elo3]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc25, hlam, hphi, p727_1, u5elo3]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hlam, p727_0]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc45, hlam, hphi, p727_1, u5elo3]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc05, hlam, hphi, p727_1, u5elo4]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc15, hlam, hphi, p727_1, u5elo4]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc25, hlam, hphi, p727_1, u5elo4]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hc35, hlam, hphi, p727_1, u5elo4]
              · have p727_0 := h727c.1
                have p727_1 := h727c.2.1
                have p727_2 := h727c.2.2.1
                have p727_3 := h727c.2.2.2
                linarith only [hlam, p727_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h753 | h753
            · linarith only [h753, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hlam, p755_0]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [h753, hc15, hlam, hphi, ht0b, ht5b, p0_1, p755_1, u0elo1]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [h720, h753, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p755_1, u1elo0]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [h720, h753, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p755_1, u1elo0]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [h720, h753, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p755_1, u1elo0]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc05, hlam, hphi, p755_1, u5elo1]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hlam, p755_0]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc25, hlam, hphi, p755_1, u5elo1]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc35, hlam, hphi, p755_1, u5elo1]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc45, hlam, hphi, p755_1, u5elo1]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc05, hlam, hphi, p755_1, u5elo2]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc15, hlam, hphi, p755_1, u5elo2]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hlam, p755_0]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc35, hlam, hphi, p755_1, u5elo2]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc45, hlam, hphi, p755_1, u5elo2]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc05, hlam, hphi, p755_1, u5elo3]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc15, hlam, hphi, p755_1, u5elo3]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc25, hlam, hphi, p755_1, u5elo3]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hlam, p755_0]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc45, hlam, hphi, p755_1, u5elo3]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc05, hlam, hphi, p755_1, u5elo4]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc15, hlam, hphi, p755_1, u5elo4]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc25, hlam, hphi, p755_1, u5elo4]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hc35, hlam, hphi, p755_1, u5elo4]
              · have p755_0 := h755c.1
                have p755_1 := h755c.2.1
                have p755_2 := h755c.2.2.1
                have p755_3 := h755c.2.2.2
                linarith only [hlam, p755_0]
      · linarith only [h721, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h782 | h782
      · rcases p0_3 (m.d 0 3) (by simp) with h783 | h783
        · linarith only [h783, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h785 | h785
          · rcases p0_3 (m.d 0 5) (by simp) with h786 | h786
            · linarith only [h720, h786, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hlam, p788_0]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [h786, hc15, hlam, hphi, ht0b, ht5b, p0_1, p788_1, u0elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [h786, hc25, hlam, hphi, ht0b, ht5b, p0_1, p788_1, u0elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [h786, hc35, hlam, hphi, ht0b, ht5b, p0_1, p788_1, u0elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [h786, hc45, hlam, hphi, ht0b, ht5b, p0_1, p788_1, u0elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc05, hlam, hphi, p788_1, u5elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hlam, p788_0]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc25, hlam, hphi, p788_1, u5elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc35, hlam, hphi, p788_1, u5elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc45, hlam, hphi, p788_1, u5elo1]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc05, hlam, hphi, p788_1, u5elo2]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc15, hlam, hphi, p788_1, u5elo2]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hlam, p788_0]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc35, hlam, hphi, p788_1, u5elo2]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc45, hlam, hphi, p788_1, u5elo2]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc05, hlam, hphi, p788_1, u5elo3]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc15, hlam, hphi, p788_1, u5elo3]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc25, hlam, hphi, p788_1, u5elo3]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hlam, p788_0]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc45, hlam, hphi, p788_1, u5elo3]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc05, hlam, hphi, p788_1, u5elo4]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc15, hlam, hphi, p788_1, u5elo4]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc25, hlam, hphi, p788_1, u5elo4]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hc35, hlam, hphi, p788_1, u5elo4]
              · have p788_0 := h788c.1
                have p788_1 := h788c.2.1
                have p788_2 := h788c.2.2.1
                have p788_3 := h788c.2.2.2
                linarith only [hlam, p788_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h814 | h814
            · linarith only [h814, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hlam, p816_0]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [h814, hc15, hlam, hphi, ht0b, ht5b, p0_1, p816_1, u0elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [h814, hc25, hlam, hphi, ht0b, ht5b, p0_1, p816_1, u0elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [h814, hc35, hlam, hphi, ht0b, ht5b, p0_1, p816_1, u0elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [h814, hc45, hlam, hphi, ht0b, ht5b, p0_1, p816_1, u0elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc05, hlam, hphi, p816_1, u5elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hlam, p816_0]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc25, hlam, hphi, p816_1, u5elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc35, hlam, hphi, p816_1, u5elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc45, hlam, hphi, p816_1, u5elo1]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc05, hlam, hphi, p816_1, u5elo2]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc15, hlam, hphi, p816_1, u5elo2]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hlam, p816_0]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc35, hlam, hphi, p816_1, u5elo2]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc45, hlam, hphi, p816_1, u5elo2]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc05, hlam, hphi, p816_1, u5elo3]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc15, hlam, hphi, p816_1, u5elo3]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc25, hlam, hphi, p816_1, u5elo3]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hlam, p816_0]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc45, hlam, hphi, p816_1, u5elo3]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc05, hlam, hphi, p816_1, u5elo4]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc15, hlam, hphi, p816_1, u5elo4]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc25, hlam, hphi, p816_1, u5elo4]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hc35, hlam, hphi, p816_1, u5elo4]
              · have p816_0 := h816c.1
                have p816_1 := h816c.2.1
                have p816_2 := h816c.2.2.1
                have p816_3 := h816c.2.2.2
                linarith only [hlam, p816_0]
      · linarith only [h782, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h843 | h843
    · rcases p0_3 (m.d 0 2) (by simp) with h844 | h844
      · rcases p0_3 (m.d 0 3) (by simp) with h845 | h845
        · rcases p0_3 (m.d 0 4) (by simp) with h846 | h846
          · linarith only [h846, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h848 | h848
            · linarith only [h848, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · rcases h5bigk with h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hlam, p850_0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [h843, h848, hc15, hlam, hphi, ht0b, ht5b, p0_1, p850_1, u0elo0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [h843, h848, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p850_1, u1elo0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [h843, h848, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p850_1, u1elo0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [h843, h848, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p850_1, u1elo0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc05, hlam, hphi, p850_1, u5elo1]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hlam, p850_0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc25, hlam, hphi, p850_1, u5elo1]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc35, hlam, hphi, p850_1, u5elo1]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc45, hlam, hphi, p850_1, u5elo1]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc05, hlam, hphi, p850_1, u5elo2]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc15, hlam, hphi, p850_1, u5elo2]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hlam, p850_0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc35, hlam, hphi, p850_1, u5elo2]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc45, hlam, hphi, p850_1, u5elo2]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc05, hlam, hphi, p850_1, u5elo3]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc15, hlam, hphi, p850_1, u5elo3]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc25, hlam, hphi, p850_1, u5elo3]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hlam, p850_0]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc45, hlam, hphi, p850_1, u5elo3]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc05, hlam, hphi, p850_1, u5elo4]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc15, hlam, hphi, p850_1, u5elo4]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc25, hlam, hphi, p850_1, u5elo4]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hc35, hlam, hphi, p850_1, u5elo4]
              · have p850_0 := h850c.1
                have p850_1 := h850c.2.1
                have p850_2 := h850c.2.2.1
                have p850_3 := h850c.2.2.2
                linarith only [hlam, p850_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h876 | h876
          · linarith only [h876, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h878 | h878
            · linarith only [h845, h878, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h878, hc15, hlam, hphi, ht0b, ht5b, p0_1, p880_1, u0elo1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h843, h878, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p880_1, u1elo0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h843, h878, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p880_1, u1elo0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h843, h878, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p880_1, u1elo0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc05, hlam, hphi, p880_1, u5elo1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc25, hlam, hphi, p880_1, u5elo1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc35, hlam, hphi, p880_1, u5elo1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc45, hlam, hphi, p880_1, u5elo1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc05, hlam, hphi, p880_1, u5elo2]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc15, hlam, hphi, p880_1, u5elo2]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc35, hlam, hphi, p880_1, u5elo2]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc45, hlam, hphi, p880_1, u5elo2]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc05, hlam, hphi, p880_1, u5elo3]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc15, hlam, hphi, p880_1, u5elo3]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc25, hlam, hphi, p880_1, u5elo3]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc45, hlam, hphi, p880_1, u5elo3]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc05, hlam, hphi, p880_1, u5elo4]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc15, hlam, hphi, p880_1, u5elo4]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc25, hlam, hphi, p880_1, u5elo4]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hc35, hlam, hphi, p880_1, u5elo4]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
      · linarith only [h844, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h907 | h907
      · rcases p0_3 (m.d 0 3) (by simp) with h908 | h908
        · rcases p0_3 (m.d 0 4) (by simp) with h909 | h909
          · linarith only [h909, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h911 | h911
            · linarith only [h843, h911, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h911, hc15, hlam, hphi, ht0b, ht5b, p0_1, p913_1, u0elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h911, hc25, hlam, hphi, ht0b, ht5b, p0_1, p913_1, u0elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h911, hc35, hlam, hphi, ht0b, ht5b, p0_1, p913_1, u0elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h911, hc45, hlam, hphi, ht0b, ht5b, p0_1, p913_1, u0elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc05, hlam, hphi, p913_1, u5elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc25, hlam, hphi, p913_1, u5elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc35, hlam, hphi, p913_1, u5elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc45, hlam, hphi, p913_1, u5elo1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc05, hlam, hphi, p913_1, u5elo2]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc15, hlam, hphi, p913_1, u5elo2]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc35, hlam, hphi, p913_1, u5elo2]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc45, hlam, hphi, p913_1, u5elo2]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc05, hlam, hphi, p913_1, u5elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc15, hlam, hphi, p913_1, u5elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc25, hlam, hphi, p913_1, u5elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc45, hlam, hphi, p913_1, u5elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc05, hlam, hphi, p913_1, u5elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc15, hlam, hphi, p913_1, u5elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc25, hlam, hphi, p913_1, u5elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hc35, hlam, hphi, p913_1, u5elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h939 | h939
          · linarith only [h939, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h941 | h941
            · linarith only [h908, h941, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hlam, p943_0]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [h941, hc15, hlam, hphi, ht0b, ht5b, p0_1, p943_1, u0elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [h941, hc25, hlam, hphi, ht0b, ht5b, p0_1, p943_1, u0elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [h941, hc35, hlam, hphi, ht0b, ht5b, p0_1, p943_1, u0elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [h941, hc45, hlam, hphi, ht0b, ht5b, p0_1, p943_1, u0elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc05, hlam, hphi, p943_1, u5elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hlam, p943_0]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc25, hlam, hphi, p943_1, u5elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc35, hlam, hphi, p943_1, u5elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc45, hlam, hphi, p943_1, u5elo1]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc05, hlam, hphi, p943_1, u5elo2]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc15, hlam, hphi, p943_1, u5elo2]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hlam, p943_0]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc35, hlam, hphi, p943_1, u5elo2]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc45, hlam, hphi, p943_1, u5elo2]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc05, hlam, hphi, p943_1, u5elo3]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc15, hlam, hphi, p943_1, u5elo3]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc25, hlam, hphi, p943_1, u5elo3]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hlam, p943_0]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc45, hlam, hphi, p943_1, u5elo3]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc05, hlam, hphi, p943_1, u5elo4]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc15, hlam, hphi, p943_1, u5elo4]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc25, hlam, hphi, p943_1, u5elo4]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hc35, hlam, hphi, p943_1, u5elo4]
              · have p943_0 := h943c.1
                have p943_1 := h943c.2.1
                have p943_2 := h943c.2.2.1
                have p943_3 := h943c.2.2.2
                linarith only [hlam, p943_0]
      · linarith only [h907, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h970 | h970
    · rcases p0_3 (m.d 0 2) (by simp) with h971 | h971
      · rcases p0_3 (m.d 0 3) (by simp) with h972 | h972
        · rcases p0_3 (m.d 0 4) (by simp) with h973 | h973
          · rcases p0_3 (m.d 0 5) (by simp) with h974 | h974
            · linarith only [h974, hlam, p0_0]
            · rcases h5bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h970, hc15, hlam, hphi, ht0b, ht5b, p0_1, p976_1, u0elo0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h970, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p976_1, u1elo0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h970, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p976_1, u1elo0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [h970, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p976_1, u1elo0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc05, hlam, hphi, p976_1, u5elo1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc25, hlam, hphi, p976_1, u5elo1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc35, hlam, hphi, p976_1, u5elo1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc45, hlam, hphi, p976_1, u5elo1]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc05, hlam, hphi, p976_1, u5elo2]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc15, hlam, hphi, p976_1, u5elo2]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc35, hlam, hphi, p976_1, u5elo2]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc45, hlam, hphi, p976_1, u5elo2]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc05, hlam, hphi, p976_1, u5elo3]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc15, hlam, hphi, p976_1, u5elo3]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc25, hlam, hphi, p976_1, u5elo3]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc45, hlam, hphi, p976_1, u5elo3]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc05, hlam, hphi, p976_1, u5elo4]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc15, hlam, hphi, p976_1, u5elo4]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc25, hlam, hphi, p976_1, u5elo4]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hc35, hlam, hphi, p976_1, u5elo4]
              · have p976_0 := h976c.1
                have p976_1 := h976c.2.1
                have p976_2 := h976c.2.2.1
                have p976_3 := h976c.2.2.2
                linarith only [hlam, p976_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1002 | h1002
            · linarith only [h1002, hlam, p0_0]
            · rcases h5bigk with h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hlam, p1004_0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc15, hlam, hphi, p1004_1, u5elo0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [h970, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1004_1, u1elo0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [h970, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1004_1, u1elo0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [h970, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1004_1, u1elo0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc05, hlam, hphi, p1004_1, u5elo1]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hlam, p1004_0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc25, hlam, hphi, p1004_1, u5elo1]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc35, hlam, hphi, p1004_1, u5elo1]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc45, hlam, hphi, p1004_1, u5elo1]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [h973, hc04, hlam, hphi, ht45, p1004_1, u5elo2]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc15, hlam, hphi, p1004_1, u5elo2]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hlam, p1004_0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc35, hlam, hphi, p1004_1, u5elo2]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc45, hlam, hphi, p1004_1, u5elo2]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [h973, hc04, hlam, hphi, ht45, p1004_1, u5elo3]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc15, hlam, hphi, p1004_1, u5elo3]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc25, hlam, hphi, p1004_1, u5elo3]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hlam, p1004_0]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc45, hlam, hphi, p1004_1, u5elo3]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [h973, hc04, hlam, hphi, ht45, p1004_1, u5elo4]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc15, hlam, hphi, p1004_1, u5elo4]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc25, hlam, hphi, p1004_1, u5elo4]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hc35, hlam, hphi, p1004_1, u5elo4]
              · have p1004_0 := h1004c.1
                have p1004_1 := h1004c.2.1
                have p1004_2 := h1004c.2.2.1
                have p1004_3 := h1004c.2.2.2
                linarith only [hlam, p1004_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1030 | h1030
          · rcases p0_3 (m.d 0 5) (by simp) with h1031 | h1031
            · linarith only [h1031, hlam, p0_0]
            · rcases h5bigk with h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hlam, hphi, p1033_1, u5elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h970, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1033_1, u1elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h970, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1033_1, u1elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h970, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1033_1, u1elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc05, hlam, hphi, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc25, hlam, hphi, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc35, hlam, hphi, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc45, hlam, hphi, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h972, hc03, hlam, hphi, ht34, ht45, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hlam, hphi, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc35, hlam, hphi, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc45, hlam, hphi, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h972, hc03, hlam, hphi, ht34, ht45, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hlam, hphi, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc25, hlam, hphi, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc45, hlam, hphi, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h972, hc03, hlam, hphi, ht34, ht45, p1033_1, u5elo4]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hlam, hphi, p1033_1, u5elo4]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc25, hlam, hphi, p1033_1, u5elo4]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc35, hlam, hphi, p1033_1, u5elo4]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1059 | h1059
            · linarith only [h1059, hlam, p0_0]
            · rcases h5bigk with h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hlam, p1061_0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc15, hlam, hphi, p1061_1, u5elo0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [h970, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1061_1, u1elo0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [h970, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1061_1, u1elo0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [h970, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1061_1, u1elo0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [h1030, hc04, hlam, hphi, ht45, p1061_1, u5elo1]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hlam, p1061_0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc25, hlam, hphi, p1061_1, u5elo1]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc35, hlam, hphi, p1061_1, u5elo1]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc45, hlam, hphi, p1061_1, u5elo1]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [h972, hc03, hlam, hphi, ht34, ht45, p1061_1, u5elo2]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc15, hlam, hphi, p1061_1, u5elo2]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hlam, p1061_0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc35, hlam, hphi, p1061_1, u5elo2]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc45, hlam, hphi, p1061_1, u5elo2]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [h972, hc03, hlam, hphi, ht34, ht45, p1061_1, u5elo3]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc15, hlam, hphi, p1061_1, u5elo3]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc25, hlam, hphi, p1061_1, u5elo3]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hlam, p1061_0]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc45, hlam, hphi, p1061_1, u5elo3]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [h972, hc03, hlam, hphi, ht34, ht45, p1061_1, u5elo4]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc15, hlam, hphi, p1061_1, u5elo4]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc25, hlam, hphi, p1061_1, u5elo4]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hc35, hlam, hphi, p1061_1, u5elo4]
              · have p1061_0 := h1061c.1
                have p1061_1 := h1061c.2.1
                have p1061_2 := h1061c.2.2.1
                have p1061_3 := h1061c.2.2.2
                linarith only [hlam, p1061_0]
      · linarith only [h971, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1088 | h1088
      · rcases p0_3 (m.d 0 3) (by simp) with h1089 | h1089
        · rcases p0_3 (m.d 0 4) (by simp) with h1090 | h1090
          · rcases p0_3 (m.d 0 5) (by simp) with h1091 | h1091
            · linarith only [h1091, hlam, p0_0]
            · rcases h5bigk with h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, p1093_1, u0elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p1093_1, u0elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p1093_1, u0elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p1093_1, u0elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc05, hlam, hphi, p1093_1, u5elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc25, hlam, hphi, p1093_1, u5elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc35, hlam, hphi, p1093_1, u5elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc45, hlam, hphi, p1093_1, u5elo1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1093_1, u5elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc15, hlam, hphi, p1093_1, u5elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc35, hlam, hphi, p1093_1, u5elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc45, hlam, hphi, p1093_1, u5elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1093_1, u5elo3]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc15, hlam, hphi, p1093_1, u5elo3]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc25, hlam, hphi, p1093_1, u5elo3]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc45, hlam, hphi, p1093_1, u5elo3]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1093_1, u5elo4]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc15, hlam, hphi, p1093_1, u5elo4]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc25, hlam, hphi, p1093_1, u5elo4]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hc35, hlam, hphi, p1093_1, u5elo4]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1119 | h1119
            · linarith only [h1119, hlam, p0_0]
            · rcases h5bigk with h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c | h1121c
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hlam, p1121_0]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc15, hlam, hphi, p1121_1, u5elo0]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p1121_1, u0elo1]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p1121_1, u0elo1]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p1121_1, u0elo1]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [h1090, hc04, hlam, hphi, ht45, p1121_1, u5elo1]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hlam, p1121_0]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc25, hlam, hphi, p1121_1, u5elo1]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc35, hlam, hphi, p1121_1, u5elo1]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc45, hlam, hphi, p1121_1, u5elo1]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1121_1, u5elo2]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc15, hlam, hphi, p1121_1, u5elo2]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hlam, p1121_0]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc35, hlam, hphi, p1121_1, u5elo2]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc45, hlam, hphi, p1121_1, u5elo2]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1121_1, u5elo3]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc15, hlam, hphi, p1121_1, u5elo3]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc25, hlam, hphi, p1121_1, u5elo3]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hlam, p1121_0]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc45, hlam, hphi, p1121_1, u5elo3]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1121_1, u5elo4]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc15, hlam, hphi, p1121_1, u5elo4]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc25, hlam, hphi, p1121_1, u5elo4]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hc35, hlam, hphi, p1121_1, u5elo4]
              · have p1121_0 := h1121c.1
                have p1121_1 := h1121c.2.1
                have p1121_2 := h1121c.2.2.1
                have p1121_3 := h1121c.2.2.2
                linarith only [hlam, p1121_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1147 | h1147
          · rcases p0_3 (m.d 0 5) (by simp) with h1148 | h1148
            · linarith only [h1148, hlam, p0_0]
            · rcases h5bigk with h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hlam, p1150_0]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc15, hlam, hphi, p1150_1, u5elo0]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p1150_1, u0elo1]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p1150_1, u0elo1]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p1150_1, u0elo1]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [h1089, hc03, hlam, hphi, ht34, ht45, p1150_1, u5elo1]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hlam, p1150_0]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc25, hlam, hphi, p1150_1, u5elo1]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc35, hlam, hphi, p1150_1, u5elo1]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc45, hlam, hphi, p1150_1, u5elo1]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo2]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc15, hlam, hphi, p1150_1, u5elo2]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hlam, p1150_0]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc35, hlam, hphi, p1150_1, u5elo2]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc45, hlam, hphi, p1150_1, u5elo2]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo3]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc15, hlam, hphi, p1150_1, u5elo3]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc25, hlam, hphi, p1150_1, u5elo3]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hlam, p1150_0]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc45, hlam, hphi, p1150_1, u5elo3]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1150_1, u5elo4]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc15, hlam, hphi, p1150_1, u5elo4]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc25, hlam, hphi, p1150_1, u5elo4]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hc35, hlam, hphi, p1150_1, u5elo4]
              · have p1150_0 := h1150c.1
                have p1150_1 := h1150c.2.1
                have p1150_2 := h1150c.2.2.1
                have p1150_3 := h1150c.2.2.2
                linarith only [hlam, p1150_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1176 | h1176
            · linarith only [h1176, hlam, p0_0]
            · rcases h5bigk with h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hlam, p1178_0]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc15, hlam, hphi, p1178_1, u5elo0]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p1178_1, u0elo1]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p1178_1, u0elo1]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p1178_1, u0elo1]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [h1147, hc04, hlam, hphi, ht45, p1178_1, u5elo1]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hlam, p1178_0]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc25, hlam, hphi, p1178_1, u5elo1]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc35, hlam, hphi, p1178_1, u5elo1]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc45, hlam, hphi, p1178_1, u5elo1]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1178_1, u5elo2]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc15, hlam, hphi, p1178_1, u5elo2]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hlam, p1178_0]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc35, hlam, hphi, p1178_1, u5elo2]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc45, hlam, hphi, p1178_1, u5elo2]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1178_1, u5elo3]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc15, hlam, hphi, p1178_1, u5elo3]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc25, hlam, hphi, p1178_1, u5elo3]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hlam, p1178_0]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc45, hlam, hphi, p1178_1, u5elo3]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [h970, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1178_1, u5elo4]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc15, hlam, hphi, p1178_1, u5elo4]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc25, hlam, hphi, p1178_1, u5elo4]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hc35, hlam, hphi, p1178_1, u5elo4]
              · have p1178_0 := h1178c.1
                have p1178_1 := h1178c.2.1
                have p1178_2 := h1178c.2.2.1
                have p1178_3 := h1178c.2.2.2
                linarith only [hlam, p1178_0]
      · linarith only [h1088, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h1205 | h1205
    · linarith only [h1205, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1207 | h1207
      · rcases p0_3 (m.d 0 3) (by simp) with h1208 | h1208
        · rcases p0_3 (m.d 0 4) (by simp) with h1209 | h1209
          · rcases p0_3 (m.d 0 5) (by simp) with h1210 | h1210
            · linarith only [h1210, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1210, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1212_1, u0elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1210, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1212_1, u0elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1210, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1212_1, u0elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1210, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1212_1, u0elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc05, hlam, hphi, p1212_1, u5elo1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc25, hlam, hphi, p1212_1, u5elo1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc35, hlam, hphi, p1212_1, u5elo1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc45, hlam, hphi, p1212_1, u5elo1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc05, hlam, hphi, p1212_1, u5elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc15, hlam, hphi, p1212_1, u5elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc35, hlam, hphi, p1212_1, u5elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc45, hlam, hphi, p1212_1, u5elo2]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc05, hlam, hphi, p1212_1, u5elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc15, hlam, hphi, p1212_1, u5elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc25, hlam, hphi, p1212_1, u5elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc45, hlam, hphi, p1212_1, u5elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc05, hlam, hphi, p1212_1, u5elo4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc15, hlam, hphi, p1212_1, u5elo4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc25, hlam, hphi, p1212_1, u5elo4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc35, hlam, hphi, p1212_1, u5elo4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1238 | h1238
            · linarith only [h1238, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hlam, p1240_0]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [h1238, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1240_1, u0elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [h1238, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1240_1, u0elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [h1238, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1240_1, u0elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [h1238, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1240_1, u0elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc05, hlam, hphi, p1240_1, u5elo1]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hlam, p1240_0]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc25, hlam, hphi, p1240_1, u5elo1]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc35, hlam, hphi, p1240_1, u5elo1]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc45, hlam, hphi, p1240_1, u5elo1]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc05, hlam, hphi, p1240_1, u5elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc15, hlam, hphi, p1240_1, u5elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hlam, p1240_0]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc35, hlam, hphi, p1240_1, u5elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc45, hlam, hphi, p1240_1, u5elo2]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc05, hlam, hphi, p1240_1, u5elo3]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc15, hlam, hphi, p1240_1, u5elo3]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc25, hlam, hphi, p1240_1, u5elo3]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hlam, p1240_0]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc45, hlam, hphi, p1240_1, u5elo3]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc05, hlam, hphi, p1240_1, u5elo4]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc15, hlam, hphi, p1240_1, u5elo4]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc25, hlam, hphi, p1240_1, u5elo4]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hc35, hlam, hphi, p1240_1, u5elo4]
              · have p1240_0 := h1240c.1
                have p1240_1 := h1240c.2.1
                have p1240_2 := h1240c.2.2.1
                have p1240_3 := h1240c.2.2.2
                linarith only [hlam, p1240_0]
        · linarith only [h1208, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1267 | h1267
        · rcases p0_3 (m.d 0 4) (by simp) with h1268 | h1268
          · rcases p0_3 (m.d 0 5) (by simp) with h1269 | h1269
            · linarith only [h1269, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c | h1271c
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hlam, p1271_0]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [h1269, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1271_1, u0elo2]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [h1268, h1269, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1271_1, u0elo3]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [h1268, h1269, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1271_1, u0elo3]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [h1268, h1269, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1271_1, u0elo3]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc05, hlam, hphi, p1271_1, u5elo1]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hlam, p1271_0]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc25, hlam, hphi, p1271_1, u5elo1]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc35, hlam, hphi, p1271_1, u5elo1]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc45, hlam, hphi, p1271_1, u5elo1]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc05, hlam, hphi, p1271_1, u5elo2]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc15, hlam, hphi, p1271_1, u5elo2]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hlam, p1271_0]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc35, hlam, hphi, p1271_1, u5elo2]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc45, hlam, hphi, p1271_1, u5elo2]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc05, hlam, hphi, p1271_1, u5elo3]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc15, hlam, hphi, p1271_1, u5elo3]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc25, hlam, hphi, p1271_1, u5elo3]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hlam, p1271_0]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc45, hlam, hphi, p1271_1, u5elo3]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc05, hlam, hphi, p1271_1, u5elo4]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc15, hlam, hphi, p1271_1, u5elo4]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc25, hlam, hphi, p1271_1, u5elo4]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hc35, hlam, hphi, p1271_1, u5elo4]
              · have p1271_0 := h1271c.1
                have p1271_1 := h1271c.2.1
                have p1271_2 := h1271c.2.2.1
                have p1271_3 := h1271c.2.2.2
                linarith only [hlam, p1271_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1297 | h1297
            · linarith only [h1297, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hlam, p1299_0]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [h1297, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1299_1, u0elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [h1297, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1299_1, u0elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [h1297, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1299_1, u0elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [h1297, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1299_1, u0elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc05, hlam, hphi, p1299_1, u5elo1]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hlam, p1299_0]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc25, hlam, hphi, p1299_1, u5elo1]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc35, hlam, hphi, p1299_1, u5elo1]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc45, hlam, hphi, p1299_1, u5elo1]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc05, hlam, hphi, p1299_1, u5elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc15, hlam, hphi, p1299_1, u5elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hlam, p1299_0]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc35, hlam, hphi, p1299_1, u5elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc45, hlam, hphi, p1299_1, u5elo2]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc05, hlam, hphi, p1299_1, u5elo3]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc15, hlam, hphi, p1299_1, u5elo3]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc25, hlam, hphi, p1299_1, u5elo3]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hlam, p1299_0]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc45, hlam, hphi, p1299_1, u5elo3]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc05, hlam, hphi, p1299_1, u5elo4]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc15, hlam, hphi, p1299_1, u5elo4]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc25, hlam, hphi, p1299_1, u5elo4]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hc35, hlam, hphi, p1299_1, u5elo4]
              · have p1299_0 := h1299c.1
                have p1299_1 := h1299c.2.1
                have p1299_2 := h1299c.2.2.1
                have p1299_3 := h1299c.2.2.2
                linarith only [hlam, p1299_0]
        · linarith only [h1267, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h1326 | h1326
    · rcases p0_3 (m.d 0 2) (by simp) with h1327 | h1327
      · linarith only [h1327, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1329 | h1329
        · rcases p0_3 (m.d 0 4) (by simp) with h1330 | h1330
          · rcases p0_3 (m.d 0 5) (by simp) with h1331 | h1331
            · linarith only [h1331, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c | h1333c
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [h1326, h1331, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1333_1, u0elo0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [h1326, h1331, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1333_1, u1elo0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [h1326, h1331, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1333_1, u1elo0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [h1326, h1331, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1333_1, u1elo0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc05, hlam, hphi, p1333_1, u5elo1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc25, hlam, hphi, p1333_1, u5elo1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc35, hlam, hphi, p1333_1, u5elo1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc45, hlam, hphi, p1333_1, u5elo1]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc05, hlam, hphi, p1333_1, u5elo2]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc15, hlam, hphi, p1333_1, u5elo2]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc35, hlam, hphi, p1333_1, u5elo2]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc45, hlam, hphi, p1333_1, u5elo2]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc05, hlam, hphi, p1333_1, u5elo3]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc15, hlam, hphi, p1333_1, u5elo3]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc25, hlam, hphi, p1333_1, u5elo3]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc45, hlam, hphi, p1333_1, u5elo3]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc05, hlam, hphi, p1333_1, u5elo4]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc15, hlam, hphi, p1333_1, u5elo4]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc25, hlam, hphi, p1333_1, u5elo4]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hc35, hlam, hphi, p1333_1, u5elo4]
              · have p1333_0 := h1333c.1
                have p1333_1 := h1333c.2.1
                have p1333_2 := h1333c.2.2.1
                have p1333_3 := h1333c.2.2.2
                linarith only [hlam, p1333_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1359 | h1359
            · linarith only [h1359, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hlam, p1361_0]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [h1359, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1361_1, u0elo2]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [h1326, h1359, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1361_1, u1elo0]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [h1326, h1359, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1361_1, u1elo0]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [h1326, h1359, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1361_1, u1elo0]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc05, hlam, hphi, p1361_1, u5elo1]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hlam, p1361_0]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc25, hlam, hphi, p1361_1, u5elo1]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc35, hlam, hphi, p1361_1, u5elo1]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc45, hlam, hphi, p1361_1, u5elo1]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc05, hlam, hphi, p1361_1, u5elo2]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc15, hlam, hphi, p1361_1, u5elo2]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hlam, p1361_0]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc35, hlam, hphi, p1361_1, u5elo2]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc45, hlam, hphi, p1361_1, u5elo2]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc05, hlam, hphi, p1361_1, u5elo3]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc15, hlam, hphi, p1361_1, u5elo3]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc25, hlam, hphi, p1361_1, u5elo3]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hlam, p1361_0]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc45, hlam, hphi, p1361_1, u5elo3]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc05, hlam, hphi, p1361_1, u5elo4]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc15, hlam, hphi, p1361_1, u5elo4]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc25, hlam, hphi, p1361_1, u5elo4]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hc35, hlam, hphi, p1361_1, u5elo4]
              · have p1361_0 := h1361c.1
                have p1361_1 := h1361c.2.1
                have p1361_2 := h1361c.2.2.1
                have p1361_3 := h1361c.2.2.2
                linarith only [hlam, p1361_0]
        · linarith only [h1329, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1388 | h1388
      · linarith only [h1388, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1390 | h1390
        · rcases p0_3 (m.d 0 4) (by simp) with h1391 | h1391
          · rcases p0_3 (m.d 0 5) (by simp) with h1392 | h1392
            · linarith only [h1326, h1392, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hlam, p1394_0]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [h1392, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1394_1, u0elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [h1392, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1394_1, u0elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [h1392, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1394_1, u0elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [h1392, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1394_1, u0elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc05, hlam, hphi, p1394_1, u5elo1]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hlam, p1394_0]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc25, hlam, hphi, p1394_1, u5elo1]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc35, hlam, hphi, p1394_1, u5elo1]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc45, hlam, hphi, p1394_1, u5elo1]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc05, hlam, hphi, p1394_1, u5elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc15, hlam, hphi, p1394_1, u5elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hlam, p1394_0]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc35, hlam, hphi, p1394_1, u5elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc45, hlam, hphi, p1394_1, u5elo2]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc05, hlam, hphi, p1394_1, u5elo3]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc15, hlam, hphi, p1394_1, u5elo3]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc25, hlam, hphi, p1394_1, u5elo3]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hlam, p1394_0]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc45, hlam, hphi, p1394_1, u5elo3]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc05, hlam, hphi, p1394_1, u5elo4]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc15, hlam, hphi, p1394_1, u5elo4]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc25, hlam, hphi, p1394_1, u5elo4]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hc35, hlam, hphi, p1394_1, u5elo4]
              · have p1394_0 := h1394c.1
                have p1394_1 := h1394c.2.1
                have p1394_2 := h1394c.2.2.1
                have p1394_3 := h1394c.2.2.2
                linarith only [hlam, p1394_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1420 | h1420
            · linarith only [h1420, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hlam, p1422_0]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [h1420, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1422_1, u0elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [h1420, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1422_1, u0elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [h1420, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1422_1, u0elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [h1420, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1422_1, u0elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc05, hlam, hphi, p1422_1, u5elo1]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hlam, p1422_0]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc25, hlam, hphi, p1422_1, u5elo1]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc35, hlam, hphi, p1422_1, u5elo1]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc45, hlam, hphi, p1422_1, u5elo1]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc05, hlam, hphi, p1422_1, u5elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc15, hlam, hphi, p1422_1, u5elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hlam, p1422_0]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc35, hlam, hphi, p1422_1, u5elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc45, hlam, hphi, p1422_1, u5elo2]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc05, hlam, hphi, p1422_1, u5elo3]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc15, hlam, hphi, p1422_1, u5elo3]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc25, hlam, hphi, p1422_1, u5elo3]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hlam, p1422_0]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc45, hlam, hphi, p1422_1, u5elo3]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc05, hlam, hphi, p1422_1, u5elo4]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc15, hlam, hphi, p1422_1, u5elo4]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc25, hlam, hphi, p1422_1, u5elo4]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hc35, hlam, hphi, p1422_1, u5elo4]
              · have p1422_0 := h1422c.1
                have p1422_1 := h1422c.2.1
                have p1422_2 := h1422c.2.2.1
                have p1422_3 := h1422c.2.2.2
                linarith only [hlam, p1422_0]
        · linarith only [h1390, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h1450 | h1450
    · rcases p0_3 (m.d 0 2) (by simp) with h1451 | h1451
      · rcases p0_3 (m.d 0 3) (by simp) with h1452 | h1452
        · rcases p0_3 (m.d 0 4) (by simp) with h1453 | h1453
          · linarith only [h1453, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1455 | h1455
            · linarith only [h1455, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hlam, p1457_0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [h1450, h1455, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1457_1, u0elo0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [h1450, h1455, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1457_1, u1elo0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [h1450, h1455, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1457_1, u1elo0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [h1450, h1455, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1457_1, u1elo0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc05, hlam, hphi, p1457_1, u5elo1]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hlam, p1457_0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc25, hlam, hphi, p1457_1, u5elo1]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc35, hlam, hphi, p1457_1, u5elo1]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc45, hlam, hphi, p1457_1, u5elo1]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc05, hlam, hphi, p1457_1, u5elo2]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc15, hlam, hphi, p1457_1, u5elo2]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hlam, p1457_0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc35, hlam, hphi, p1457_1, u5elo2]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc45, hlam, hphi, p1457_1, u5elo2]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc05, hlam, hphi, p1457_1, u5elo3]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc15, hlam, hphi, p1457_1, u5elo3]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc25, hlam, hphi, p1457_1, u5elo3]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hlam, p1457_0]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc45, hlam, hphi, p1457_1, u5elo3]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc05, hlam, hphi, p1457_1, u5elo4]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc15, hlam, hphi, p1457_1, u5elo4]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc25, hlam, hphi, p1457_1, u5elo4]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hc35, hlam, hphi, p1457_1, u5elo4]
              · have p1457_0 := h1457c.1
                have p1457_1 := h1457c.2.1
                have p1457_2 := h1457c.2.2.1
                have p1457_3 := h1457c.2.2.2
                linarith only [hlam, p1457_0]
        · linarith only [h1452, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1484 | h1484
        · rcases p0_3 (m.d 0 4) (by simp) with h1485 | h1485
          · linarith only [h1485, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1487 | h1487
            · linarith only [h1451, h1487, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hlam, p1489_0]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [h1487, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1489_1, u0elo2]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [h1450, h1487, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1489_1, u1elo0]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [h1450, h1487, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1489_1, u1elo0]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [h1450, h1487, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1489_1, u1elo0]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc05, hlam, hphi, p1489_1, u5elo1]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hlam, p1489_0]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc25, hlam, hphi, p1489_1, u5elo1]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc35, hlam, hphi, p1489_1, u5elo1]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc45, hlam, hphi, p1489_1, u5elo1]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc05, hlam, hphi, p1489_1, u5elo2]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc15, hlam, hphi, p1489_1, u5elo2]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hlam, p1489_0]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc35, hlam, hphi, p1489_1, u5elo2]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc45, hlam, hphi, p1489_1, u5elo2]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc05, hlam, hphi, p1489_1, u5elo3]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc15, hlam, hphi, p1489_1, u5elo3]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc25, hlam, hphi, p1489_1, u5elo3]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hlam, p1489_0]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc45, hlam, hphi, p1489_1, u5elo3]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc05, hlam, hphi, p1489_1, u5elo4]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc15, hlam, hphi, p1489_1, u5elo4]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc25, hlam, hphi, p1489_1, u5elo4]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hc35, hlam, hphi, p1489_1, u5elo4]
              · have p1489_0 := h1489c.1
                have p1489_1 := h1489c.2.1
                have p1489_2 := h1489c.2.2.1
                have p1489_3 := h1489c.2.2.2
                linarith only [hlam, p1489_0]
        · linarith only [h1484, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1516 | h1516
      · rcases p0_3 (m.d 0 3) (by simp) with h1517 | h1517
        · rcases p0_3 (m.d 0 4) (by simp) with h1518 | h1518
          · linarith only [h1518, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1520 | h1520
            · linarith only [h1450, h1520, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hlam, p1522_0]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [h1516, h1520, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1522_1, u0elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [h1516, h1520, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1522_1, u0elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [h1516, h1520, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1522_1, u0elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [h1516, h1520, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1522_1, u0elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc05, hlam, hphi, p1522_1, u5elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hlam, p1522_0]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc25, hlam, hphi, p1522_1, u5elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc35, hlam, hphi, p1522_1, u5elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc45, hlam, hphi, p1522_1, u5elo1]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc05, hlam, hphi, p1522_1, u5elo2]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc15, hlam, hphi, p1522_1, u5elo2]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hlam, p1522_0]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc35, hlam, hphi, p1522_1, u5elo2]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc45, hlam, hphi, p1522_1, u5elo2]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc05, hlam, hphi, p1522_1, u5elo3]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc15, hlam, hphi, p1522_1, u5elo3]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc25, hlam, hphi, p1522_1, u5elo3]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hlam, p1522_0]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc45, hlam, hphi, p1522_1, u5elo3]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc05, hlam, hphi, p1522_1, u5elo4]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc15, hlam, hphi, p1522_1, u5elo4]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc25, hlam, hphi, p1522_1, u5elo4]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hc35, hlam, hphi, p1522_1, u5elo4]
              · have p1522_0 := h1522c.1
                have p1522_1 := h1522c.2.1
                have p1522_2 := h1522c.2.2.1
                have p1522_3 := h1522c.2.2.2
                linarith only [hlam, p1522_0]
        · linarith only [h1517, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1549 | h1549
        · rcases p0_3 (m.d 0 4) (by simp) with h1550 | h1550
          · linarith only [h1550, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1552 | h1552
            · linarith only [h1516, h1552, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hlam, p1554_0]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [h1552, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1554_1, u0elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [h1552, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1554_1, u0elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [h1552, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1554_1, u0elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [h1552, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1554_1, u0elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc05, hlam, hphi, p1554_1, u5elo1]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hlam, p1554_0]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc25, hlam, hphi, p1554_1, u5elo1]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc35, hlam, hphi, p1554_1, u5elo1]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc45, hlam, hphi, p1554_1, u5elo1]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc05, hlam, hphi, p1554_1, u5elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc15, hlam, hphi, p1554_1, u5elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hlam, p1554_0]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc35, hlam, hphi, p1554_1, u5elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc45, hlam, hphi, p1554_1, u5elo2]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc05, hlam, hphi, p1554_1, u5elo3]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc15, hlam, hphi, p1554_1, u5elo3]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc25, hlam, hphi, p1554_1, u5elo3]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hlam, p1554_0]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc45, hlam, hphi, p1554_1, u5elo3]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc05, hlam, hphi, p1554_1, u5elo4]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc15, hlam, hphi, p1554_1, u5elo4]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc25, hlam, hphi, p1554_1, u5elo4]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hc35, hlam, hphi, p1554_1, u5elo4]
              · have p1554_0 := h1554c.1
                have p1554_1 := h1554c.2.1
                have p1554_2 := h1554c.2.2.1
                have p1554_3 := h1554c.2.2.2
                linarith only [hlam, p1554_0]
        · linarith only [h1549, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h1581 | h1581
    · rcases p0_3 (m.d 0 2) (by simp) with h1582 | h1582
      · rcases p0_3 (m.d 0 3) (by simp) with h1583 | h1583
        · rcases p0_3 (m.d 0 4) (by simp) with h1584 | h1584
          · rcases p0_3 (m.d 0 5) (by simp) with h1585 | h1585
            · linarith only [h1585, hlam, p0_0]
            · rcases h5bigk with h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hlam, p1587_0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [h1581, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1587_1, u0elo0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [h1581, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1587_1, u1elo0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [h1581, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1587_1, u1elo0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [h1581, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1587_1, u1elo0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc05, hlam, hphi, p1587_1, u5elo1]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hlam, p1587_0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc25, hlam, hphi, p1587_1, u5elo1]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc35, hlam, hphi, p1587_1, u5elo1]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc45, hlam, hphi, p1587_1, u5elo1]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc05, hlam, hphi, p1587_1, u5elo2]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc15, hlam, hphi, p1587_1, u5elo2]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hlam, p1587_0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc35, hlam, hphi, p1587_1, u5elo2]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc45, hlam, hphi, p1587_1, u5elo2]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc05, hlam, hphi, p1587_1, u5elo3]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc15, hlam, hphi, p1587_1, u5elo3]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc25, hlam, hphi, p1587_1, u5elo3]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hlam, p1587_0]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc45, hlam, hphi, p1587_1, u5elo3]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc05, hlam, hphi, p1587_1, u5elo4]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc15, hlam, hphi, p1587_1, u5elo4]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc25, hlam, hphi, p1587_1, u5elo4]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hc35, hlam, hphi, p1587_1, u5elo4]
              · have p1587_0 := h1587c.1
                have p1587_1 := h1587c.2.1
                have p1587_2 := h1587c.2.2.1
                have p1587_3 := h1587c.2.2.2
                linarith only [hlam, p1587_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1613 | h1613
            · linarith only [h1613, hlam, p0_0]
            · rcases h5bigk with h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hlam, p1615_0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc15, hlam, hphi, p1615_1, u5elo0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [h1581, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1615_1, u1elo0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [h1581, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1615_1, u1elo0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [h1581, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1615_1, u1elo0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc05, hlam, hphi, p1615_1, u5elo1]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hlam, p1615_0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc25, hlam, hphi, p1615_1, u5elo1]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc35, hlam, hphi, p1615_1, u5elo1]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc45, hlam, hphi, p1615_1, u5elo1]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [h1584, hc04, hlam, hphi, ht45, p1615_1, u5elo2]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc15, hlam, hphi, p1615_1, u5elo2]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hlam, p1615_0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc35, hlam, hphi, p1615_1, u5elo2]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc45, hlam, hphi, p1615_1, u5elo2]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [h1584, hc04, hlam, hphi, ht45, p1615_1, u5elo3]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc15, hlam, hphi, p1615_1, u5elo3]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc25, hlam, hphi, p1615_1, u5elo3]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hlam, p1615_0]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc45, hlam, hphi, p1615_1, u5elo3]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [h1584, hc04, hlam, hphi, ht45, p1615_1, u5elo4]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc15, hlam, hphi, p1615_1, u5elo4]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc25, hlam, hphi, p1615_1, u5elo4]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hc35, hlam, hphi, p1615_1, u5elo4]
              · have p1615_0 := h1615c.1
                have p1615_1 := h1615c.2.1
                have p1615_2 := h1615c.2.2.1
                have p1615_3 := h1615c.2.2.2
                linarith only [hlam, p1615_0]
        · linarith only [h1583, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1642 | h1642
        · rcases p0_3 (m.d 0 4) (by simp) with h1643 | h1643
          · rcases p0_3 (m.d 0 5) (by simp) with h1644 | h1644
            · linarith only [h1644, hlam, p0_0]
            · rcases h5bigk with h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hlam, p1646_0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc15, hlam, hphi, p1646_1, u5elo0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [h1581, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1646_1, u1elo0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [h1581, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1646_1, u1elo0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [h1581, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1646_1, u1elo0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc05, hlam, hphi, p1646_1, u5elo1]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hlam, p1646_0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc25, hlam, hphi, p1646_1, u5elo1]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc35, hlam, hphi, p1646_1, u5elo1]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc45, hlam, hphi, p1646_1, u5elo1]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [h1582, hc02, hlam, hphi, ht23, ht34, ht45, p1646_1, u5elo2]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc15, hlam, hphi, p1646_1, u5elo2]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hlam, p1646_0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc35, hlam, hphi, p1646_1, u5elo2]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc45, hlam, hphi, p1646_1, u5elo2]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [h1582, hc02, hlam, hphi, ht23, ht34, ht45, p1646_1, u5elo3]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc15, hlam, hphi, p1646_1, u5elo3]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc25, hlam, hphi, p1646_1, u5elo3]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hlam, p1646_0]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc45, hlam, hphi, p1646_1, u5elo3]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [h1582, hc02, hlam, hphi, ht23, ht34, ht45, p1646_1, u5elo4]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc15, hlam, hphi, p1646_1, u5elo4]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc25, hlam, hphi, p1646_1, u5elo4]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hc35, hlam, hphi, p1646_1, u5elo4]
              · have p1646_0 := h1646c.1
                have p1646_1 := h1646c.2.1
                have p1646_2 := h1646c.2.2.1
                have p1646_3 := h1646c.2.2.2
                linarith only [hlam, p1646_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1672 | h1672
            · linarith only [h1672, hlam, p0_0]
            · rcases h5bigk with h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c | h1674c
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hlam, p1674_0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc15, hlam, hphi, p1674_1, u5elo0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [h1581, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1674_1, u1elo0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [h1581, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1674_1, u1elo0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [h1581, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1674_1, u1elo0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [h1643, hc04, hlam, hphi, ht45, p1674_1, u5elo1]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hlam, p1674_0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc25, hlam, hphi, p1674_1, u5elo1]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc35, hlam, hphi, p1674_1, u5elo1]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc45, hlam, hphi, p1674_1, u5elo1]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [h1582, hc02, hlam, hphi, ht23, ht34, ht45, p1674_1, u5elo2]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc15, hlam, hphi, p1674_1, u5elo2]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hlam, p1674_0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc35, hlam, hphi, p1674_1, u5elo2]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc45, hlam, hphi, p1674_1, u5elo2]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [h1582, hc02, hlam, hphi, ht23, ht34, ht45, p1674_1, u5elo3]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc15, hlam, hphi, p1674_1, u5elo3]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc25, hlam, hphi, p1674_1, u5elo3]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hlam, p1674_0]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc45, hlam, hphi, p1674_1, u5elo3]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [h1582, hc02, hlam, hphi, ht23, ht34, ht45, p1674_1, u5elo4]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc15, hlam, hphi, p1674_1, u5elo4]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc25, hlam, hphi, p1674_1, u5elo4]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hc35, hlam, hphi, p1674_1, u5elo4]
              · have p1674_0 := h1674c.1
                have p1674_1 := h1674c.2.1
                have p1674_2 := h1674c.2.2.1
                have p1674_3 := h1674c.2.2.2
                linarith only [hlam, p1674_0]
        · linarith only [h1642, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1701 | h1701
      · rcases p0_3 (m.d 0 3) (by simp) with h1702 | h1702
        · rcases p0_3 (m.d 0 4) (by simp) with h1703 | h1703
          · rcases p0_3 (m.d 0 5) (by simp) with h1704 | h1704
            · linarith only [h1704, hlam, p0_0]
            · rcases h5bigk with h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c | h1706c
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hlam, p1706_0]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [h1701, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1706_1, u0elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [h1701, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1706_1, u0elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [h1701, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1706_1, u0elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [h1701, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1706_1, u0elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc05, hlam, hphi, p1706_1, u5elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hlam, p1706_0]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc25, hlam, hphi, p1706_1, u5elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc35, hlam, hphi, p1706_1, u5elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc45, hlam, hphi, p1706_1, u5elo1]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1706_1, u5elo2]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc15, hlam, hphi, p1706_1, u5elo2]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hlam, p1706_0]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc35, hlam, hphi, p1706_1, u5elo2]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc45, hlam, hphi, p1706_1, u5elo2]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1706_1, u5elo3]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc15, hlam, hphi, p1706_1, u5elo3]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc25, hlam, hphi, p1706_1, u5elo3]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hlam, p1706_0]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc45, hlam, hphi, p1706_1, u5elo3]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1706_1, u5elo4]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc15, hlam, hphi, p1706_1, u5elo4]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc25, hlam, hphi, p1706_1, u5elo4]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hc35, hlam, hphi, p1706_1, u5elo4]
              · have p1706_0 := h1706c.1
                have p1706_1 := h1706c.2.1
                have p1706_2 := h1706c.2.2.1
                have p1706_3 := h1706c.2.2.2
                linarith only [hlam, p1706_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1732 | h1732
            · linarith only [h1732, hlam, p0_0]
            · rcases h5bigk with h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hlam, p1734_0]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc15, hlam, hphi, p1734_1, u5elo0]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [h1701, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1734_1, u0elo1]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [h1701, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1734_1, u0elo1]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [h1701, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1734_1, u0elo1]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [h1703, hc04, hlam, hphi, ht45, p1734_1, u5elo1]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hlam, p1734_0]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc25, hlam, hphi, p1734_1, u5elo1]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc35, hlam, hphi, p1734_1, u5elo1]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc45, hlam, hphi, p1734_1, u5elo1]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1734_1, u5elo2]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc15, hlam, hphi, p1734_1, u5elo2]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hlam, p1734_0]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc35, hlam, hphi, p1734_1, u5elo2]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc45, hlam, hphi, p1734_1, u5elo2]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1734_1, u5elo3]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc15, hlam, hphi, p1734_1, u5elo3]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc25, hlam, hphi, p1734_1, u5elo3]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hlam, p1734_0]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc45, hlam, hphi, p1734_1, u5elo3]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1734_1, u5elo4]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc15, hlam, hphi, p1734_1, u5elo4]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc25, hlam, hphi, p1734_1, u5elo4]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hc35, hlam, hphi, p1734_1, u5elo4]
              · have p1734_0 := h1734c.1
                have p1734_1 := h1734c.2.1
                have p1734_2 := h1734c.2.2.1
                have p1734_3 := h1734c.2.2.2
                linarith only [hlam, p1734_0]
        · linarith only [h1702, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1761 | h1761
        · rcases p0_3 (m.d 0 4) (by simp) with h1762 | h1762
          · rcases p0_3 (m.d 0 5) (by simp) with h1763 | h1763
            · linarith only [h1763, hlam, p0_0]
            · rcases h5bigk with h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hlam, p1765_0]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc15, hlam, hphi, p1765_1, u5elo0]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p1765_1, u0elo2]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p1765_1, u0elo2]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p1765_1, u0elo2]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [h1701, hc02, hlam, hphi, ht23, ht34, ht45, p1765_1, u5elo1]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hlam, p1765_0]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc25, hlam, hphi, p1765_1, u5elo1]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc35, hlam, hphi, p1765_1, u5elo1]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc45, hlam, hphi, p1765_1, u5elo1]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1765_1, u5elo2]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc15, hlam, hphi, p1765_1, u5elo2]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hlam, p1765_0]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc35, hlam, hphi, p1765_1, u5elo2]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc45, hlam, hphi, p1765_1, u5elo2]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1765_1, u5elo3]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc15, hlam, hphi, p1765_1, u5elo3]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc25, hlam, hphi, p1765_1, u5elo3]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hlam, p1765_0]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc45, hlam, hphi, p1765_1, u5elo3]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1765_1, u5elo4]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc15, hlam, hphi, p1765_1, u5elo4]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc25, hlam, hphi, p1765_1, u5elo4]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hc35, hlam, hphi, p1765_1, u5elo4]
              · have p1765_0 := h1765c.1
                have p1765_1 := h1765c.2.1
                have p1765_2 := h1765c.2.2.1
                have p1765_3 := h1765c.2.2.2
                linarith only [hlam, p1765_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1791 | h1791
            · linarith only [h1791, hlam, p0_0]
            · rcases h5bigk with h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hlam, p1793_0]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc15, hlam, hphi, p1793_1, u5elo0]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p1793_1, u0elo2]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p1793_1, u0elo2]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p1793_1, u0elo2]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [h1762, hc04, hlam, hphi, ht45, p1793_1, u5elo1]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hlam, p1793_0]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc25, hlam, hphi, p1793_1, u5elo1]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc35, hlam, hphi, p1793_1, u5elo1]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc45, hlam, hphi, p1793_1, u5elo1]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1793_1, u5elo2]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc15, hlam, hphi, p1793_1, u5elo2]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hlam, p1793_0]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc35, hlam, hphi, p1793_1, u5elo2]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc45, hlam, hphi, p1793_1, u5elo2]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1793_1, u5elo3]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc15, hlam, hphi, p1793_1, u5elo3]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc25, hlam, hphi, p1793_1, u5elo3]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hlam, p1793_0]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc45, hlam, hphi, p1793_1, u5elo3]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [h1581, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1793_1, u5elo4]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc15, hlam, hphi, p1793_1, u5elo4]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc25, hlam, hphi, p1793_1, u5elo4]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hc35, hlam, hphi, p1793_1, u5elo4]
              · have p1793_0 := h1793c.1
                have p1793_1 := h1793c.2.1
                have p1793_2 := h1793c.2.2.1
                have p1793_3 := h1793c.2.2.2
                linarith only [hlam, p1793_0]
        · linarith only [h1761, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h1820 | h1820
    · linarith only [h1820, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1822 | h1822
      · rcases p0_3 (m.d 0 3) (by simp) with h1823 | h1823
        · rcases p0_3 (m.d 0 4) (by simp) with h1824 | h1824
          · rcases p0_3 (m.d 0 5) (by simp) with h1825 | h1825
            · linarith only [h1825, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c | h1827c
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hlam, p1827_0]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [h1822, h1825, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1827_1, u0elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [h1822, h1825, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1827_1, u0elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [h1822, h1825, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1827_1, u0elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [h1822, h1825, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1827_1, u0elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc05, hlam, hphi, p1827_1, u5elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hlam, p1827_0]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc25, hlam, hphi, p1827_1, u5elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc35, hlam, hphi, p1827_1, u5elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc45, hlam, hphi, p1827_1, u5elo1]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc05, hlam, hphi, p1827_1, u5elo2]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc15, hlam, hphi, p1827_1, u5elo2]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hlam, p1827_0]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc35, hlam, hphi, p1827_1, u5elo2]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc45, hlam, hphi, p1827_1, u5elo2]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc05, hlam, hphi, p1827_1, u5elo3]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc15, hlam, hphi, p1827_1, u5elo3]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc25, hlam, hphi, p1827_1, u5elo3]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hlam, p1827_0]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc45, hlam, hphi, p1827_1, u5elo3]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc05, hlam, hphi, p1827_1, u5elo4]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc15, hlam, hphi, p1827_1, u5elo4]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc25, hlam, hphi, p1827_1, u5elo4]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hc35, hlam, hphi, p1827_1, u5elo4]
              · have p1827_0 := h1827c.1
                have p1827_1 := h1827c.2.1
                have p1827_2 := h1827c.2.2.1
                have p1827_3 := h1827c.2.2.2
                linarith only [hlam, p1827_0]
          · linarith only [h1824, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1854 | h1854
          · rcases p0_3 (m.d 0 5) (by simp) with h1855 | h1855
            · linarith only [h1855, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c | h1857c
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hlam, p1857_0]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [h1822, h1855, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1857_1, u0elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [h1822, h1855, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1857_1, u0elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [h1822, h1855, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1857_1, u0elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [h1822, h1855, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1857_1, u0elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc05, hlam, hphi, p1857_1, u5elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hlam, p1857_0]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc25, hlam, hphi, p1857_1, u5elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc35, hlam, hphi, p1857_1, u5elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc45, hlam, hphi, p1857_1, u5elo1]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc05, hlam, hphi, p1857_1, u5elo2]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc15, hlam, hphi, p1857_1, u5elo2]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hlam, p1857_0]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc35, hlam, hphi, p1857_1, u5elo2]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc45, hlam, hphi, p1857_1, u5elo2]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc05, hlam, hphi, p1857_1, u5elo3]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc15, hlam, hphi, p1857_1, u5elo3]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc25, hlam, hphi, p1857_1, u5elo3]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hlam, p1857_0]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc45, hlam, hphi, p1857_1, u5elo3]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc05, hlam, hphi, p1857_1, u5elo4]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc15, hlam, hphi, p1857_1, u5elo4]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc25, hlam, hphi, p1857_1, u5elo4]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hc35, hlam, hphi, p1857_1, u5elo4]
              · have p1857_0 := h1857c.1
                have p1857_1 := h1857c.2.1
                have p1857_2 := h1857c.2.2.1
                have p1857_3 := h1857c.2.2.2
                linarith only [hlam, p1857_0]
          · linarith only [h1854, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1884 | h1884
        · rcases p0_3 (m.d 0 4) (by simp) with h1885 | h1885
          · rcases p0_3 (m.d 0 5) (by simp) with h1886 | h1886
            · linarith only [h1886, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c | h1888c
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hlam, p1888_0]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [h1884, h1886, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1888_1, u0elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [h1884, h1886, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1888_1, u0elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [h1884, h1886, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1888_1, u0elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [h1884, h1886, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1888_1, u0elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc05, hlam, hphi, p1888_1, u5elo1]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hlam, p1888_0]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc25, hlam, hphi, p1888_1, u5elo1]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc35, hlam, hphi, p1888_1, u5elo1]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc45, hlam, hphi, p1888_1, u5elo1]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc05, hlam, hphi, p1888_1, u5elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc15, hlam, hphi, p1888_1, u5elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hlam, p1888_0]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc35, hlam, hphi, p1888_1, u5elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc45, hlam, hphi, p1888_1, u5elo2]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc05, hlam, hphi, p1888_1, u5elo3]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc15, hlam, hphi, p1888_1, u5elo3]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc25, hlam, hphi, p1888_1, u5elo3]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hlam, p1888_0]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc45, hlam, hphi, p1888_1, u5elo3]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc05, hlam, hphi, p1888_1, u5elo4]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc15, hlam, hphi, p1888_1, u5elo4]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc25, hlam, hphi, p1888_1, u5elo4]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hc35, hlam, hphi, p1888_1, u5elo4]
              · have p1888_0 := h1888c.1
                have p1888_1 := h1888c.2.1
                have p1888_2 := h1888c.2.2.1
                have p1888_3 := h1888c.2.2.2
                linarith only [hlam, p1888_0]
          · linarith only [h1885, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1915 | h1915
          · rcases p0_3 (m.d 0 5) (by simp) with h1916 | h1916
            · linarith only [h1916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hlam, p1918_0]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [h1916, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1918_1, u0elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [h1916, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1918_1, u0elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [h1916, hc35, hlam, hphi, ht0b, ht5b, p0_1, p1918_1, u0elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [h1916, hc45, hlam, hphi, ht0b, ht5b, p0_1, p1918_1, u0elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc05, hlam, hphi, p1918_1, u5elo1]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hlam, p1918_0]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc25, hlam, hphi, p1918_1, u5elo1]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc35, hlam, hphi, p1918_1, u5elo1]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc45, hlam, hphi, p1918_1, u5elo1]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc05, hlam, hphi, p1918_1, u5elo2]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc15, hlam, hphi, p1918_1, u5elo2]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hlam, p1918_0]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc35, hlam, hphi, p1918_1, u5elo2]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc45, hlam, hphi, p1918_1, u5elo2]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc05, hlam, hphi, p1918_1, u5elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc15, hlam, hphi, p1918_1, u5elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc25, hlam, hphi, p1918_1, u5elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hlam, p1918_0]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc45, hlam, hphi, p1918_1, u5elo3]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc05, hlam, hphi, p1918_1, u5elo4]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc15, hlam, hphi, p1918_1, u5elo4]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc25, hlam, hphi, p1918_1, u5elo4]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hc35, hlam, hphi, p1918_1, u5elo4]
              · have p1918_0 := h1918c.1
                have p1918_1 := h1918c.2.1
                have p1918_2 := h1918c.2.2.1
                have p1918_3 := h1918c.2.2.2
                linarith only [hlam, p1918_0]
          · linarith only [h1915, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h1945 | h1945
    · rcases p0_3 (m.d 0 2) (by simp) with h1946 | h1946
      · linarith only [h1946, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1948 | h1948
        · rcases p0_3 (m.d 0 4) (by simp) with h1949 | h1949
          · rcases p0_3 (m.d 0 5) (by simp) with h1950 | h1950
            · linarith only [h1950, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hlam, p1952_0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [h1945, h1950, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1952_1, u0elo0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [h1945, h1950, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1952_1, u1elo0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [h1945, h1950, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1952_1, u1elo0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [h1945, h1950, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1952_1, u1elo0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc05, hlam, hphi, p1952_1, u5elo1]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hlam, p1952_0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc25, hlam, hphi, p1952_1, u5elo1]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc35, hlam, hphi, p1952_1, u5elo1]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc45, hlam, hphi, p1952_1, u5elo1]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc05, hlam, hphi, p1952_1, u5elo2]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc15, hlam, hphi, p1952_1, u5elo2]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hlam, p1952_0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc35, hlam, hphi, p1952_1, u5elo2]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc45, hlam, hphi, p1952_1, u5elo2]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc05, hlam, hphi, p1952_1, u5elo3]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc15, hlam, hphi, p1952_1, u5elo3]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc25, hlam, hphi, p1952_1, u5elo3]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hlam, p1952_0]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc45, hlam, hphi, p1952_1, u5elo3]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc05, hlam, hphi, p1952_1, u5elo4]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc15, hlam, hphi, p1952_1, u5elo4]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc25, hlam, hphi, p1952_1, u5elo4]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hc35, hlam, hphi, p1952_1, u5elo4]
              · have p1952_0 := h1952c.1
                have p1952_1 := h1952c.2.1
                have p1952_2 := h1952c.2.2.1
                have p1952_3 := h1952c.2.2.2
                linarith only [hlam, p1952_0]
          · linarith only [h1949, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1979 | h1979
          · rcases p0_3 (m.d 0 5) (by simp) with h1980 | h1980
            · linarith only [h1980, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hlam, p1982_0]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [h1980, hc15, hlam, hphi, ht0b, ht5b, p0_1, p1982_1, u0elo3]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [h1945, h1980, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1982_1, u1elo0]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [h1945, h1980, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1982_1, u1elo0]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [h1945, h1980, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1982_1, u1elo0]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc05, hlam, hphi, p1982_1, u5elo1]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hlam, p1982_0]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc25, hlam, hphi, p1982_1, u5elo1]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc35, hlam, hphi, p1982_1, u5elo1]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc45, hlam, hphi, p1982_1, u5elo1]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc05, hlam, hphi, p1982_1, u5elo2]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc15, hlam, hphi, p1982_1, u5elo2]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hlam, p1982_0]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc35, hlam, hphi, p1982_1, u5elo2]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc45, hlam, hphi, p1982_1, u5elo2]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc05, hlam, hphi, p1982_1, u5elo3]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc15, hlam, hphi, p1982_1, u5elo3]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc25, hlam, hphi, p1982_1, u5elo3]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hlam, p1982_0]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc45, hlam, hphi, p1982_1, u5elo3]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc05, hlam, hphi, p1982_1, u5elo4]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc15, hlam, hphi, p1982_1, u5elo4]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc25, hlam, hphi, p1982_1, u5elo4]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hc35, hlam, hphi, p1982_1, u5elo4]
              · have p1982_0 := h1982c.1
                have p1982_1 := h1982c.2.1
                have p1982_2 := h1982c.2.2.1
                have p1982_3 := h1982c.2.2.2
                linarith only [hlam, p1982_0]
          · linarith only [h1979, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2009 | h2009
      · linarith only [h2009, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2011 | h2011
        · rcases p0_3 (m.d 0 4) (by simp) with h2012 | h2012
          · rcases p0_3 (m.d 0 5) (by simp) with h2013 | h2013
            · linarith only [h1945, h2013, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hlam, p2015_0]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [h2011, h2013, hc15, hlam, hphi, ht0b, ht5b, p0_1, p2015_1, u0elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [h2011, h2013, hc25, hlam, hphi, ht0b, ht5b, p0_1, p2015_1, u0elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [h2011, h2013, hc35, hlam, hphi, ht0b, ht5b, p0_1, p2015_1, u0elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [h2011, h2013, hc45, hlam, hphi, ht0b, ht5b, p0_1, p2015_1, u0elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc05, hlam, hphi, p2015_1, u5elo1]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hlam, p2015_0]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc25, hlam, hphi, p2015_1, u5elo1]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc35, hlam, hphi, p2015_1, u5elo1]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc45, hlam, hphi, p2015_1, u5elo1]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc05, hlam, hphi, p2015_1, u5elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc15, hlam, hphi, p2015_1, u5elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hlam, p2015_0]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc35, hlam, hphi, p2015_1, u5elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc45, hlam, hphi, p2015_1, u5elo2]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc05, hlam, hphi, p2015_1, u5elo3]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc15, hlam, hphi, p2015_1, u5elo3]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc25, hlam, hphi, p2015_1, u5elo3]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hlam, p2015_0]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc45, hlam, hphi, p2015_1, u5elo3]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc05, hlam, hphi, p2015_1, u5elo4]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc15, hlam, hphi, p2015_1, u5elo4]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc25, hlam, hphi, p2015_1, u5elo4]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hc35, hlam, hphi, p2015_1, u5elo4]
              · have p2015_0 := h2015c.1
                have p2015_1 := h2015c.2.1
                have p2015_2 := h2015c.2.2.1
                have p2015_3 := h2015c.2.2.2
                linarith only [hlam, p2015_0]
          · linarith only [h2012, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2042 | h2042
          · rcases p0_3 (m.d 0 5) (by simp) with h2043 | h2043
            · linarith only [h2043, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hlam, p2045_0]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [h2043, hc15, hlam, hphi, ht0b, ht5b, p0_1, p2045_1, u0elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [h2043, hc25, hlam, hphi, ht0b, ht5b, p0_1, p2045_1, u0elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [h2043, hc35, hlam, hphi, ht0b, ht5b, p0_1, p2045_1, u0elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [h2043, hc45, hlam, hphi, ht0b, ht5b, p0_1, p2045_1, u0elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc05, hlam, hphi, p2045_1, u5elo1]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hlam, p2045_0]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc25, hlam, hphi, p2045_1, u5elo1]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc35, hlam, hphi, p2045_1, u5elo1]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc45, hlam, hphi, p2045_1, u5elo1]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc05, hlam, hphi, p2045_1, u5elo2]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc15, hlam, hphi, p2045_1, u5elo2]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hlam, p2045_0]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc35, hlam, hphi, p2045_1, u5elo2]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc45, hlam, hphi, p2045_1, u5elo2]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc05, hlam, hphi, p2045_1, u5elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc15, hlam, hphi, p2045_1, u5elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc25, hlam, hphi, p2045_1, u5elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hlam, p2045_0]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc45, hlam, hphi, p2045_1, u5elo3]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc05, hlam, hphi, p2045_1, u5elo4]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc15, hlam, hphi, p2045_1, u5elo4]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc25, hlam, hphi, p2045_1, u5elo4]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hc35, hlam, hphi, p2045_1, u5elo4]
              · have p2045_0 := h2045c.1
                have p2045_1 := h2045c.2.1
                have p2045_2 := h2045c.2.2.1
                have p2045_3 := h2045c.2.2.2
                linarith only [hlam, p2045_0]
          · linarith only [h2042, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2072 | h2072
    · rcases p0_3 (m.d 0 2) (by simp) with h2073 | h2073
      · rcases p0_3 (m.d 0 3) (by simp) with h2074 | h2074
        · linarith only [h2074, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2076 | h2076
          · rcases p0_3 (m.d 0 5) (by simp) with h2077 | h2077
            · linarith only [h2077, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hlam, p2079_0]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [h2073, h2077, hc15, hlam, hphi, ht0b, ht5b, p0_1, p2079_1, u0elo1]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [h2072, h2077, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2079_1, u1elo0]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [h2072, h2077, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2079_1, u1elo0]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [h2072, h2077, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2079_1, u1elo0]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc05, hlam, hphi, p2079_1, u5elo1]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hlam, p2079_0]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc25, hlam, hphi, p2079_1, u5elo1]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc35, hlam, hphi, p2079_1, u5elo1]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc45, hlam, hphi, p2079_1, u5elo1]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc05, hlam, hphi, p2079_1, u5elo2]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc15, hlam, hphi, p2079_1, u5elo2]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hlam, p2079_0]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc35, hlam, hphi, p2079_1, u5elo2]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc45, hlam, hphi, p2079_1, u5elo2]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc05, hlam, hphi, p2079_1, u5elo3]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc15, hlam, hphi, p2079_1, u5elo3]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc25, hlam, hphi, p2079_1, u5elo3]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hlam, p2079_0]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc45, hlam, hphi, p2079_1, u5elo3]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc05, hlam, hphi, p2079_1, u5elo4]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc15, hlam, hphi, p2079_1, u5elo4]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc25, hlam, hphi, p2079_1, u5elo4]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hc35, hlam, hphi, p2079_1, u5elo4]
              · have p2079_0 := h2079c.1
                have p2079_1 := h2079c.2.1
                have p2079_2 := h2079c.2.2.1
                have p2079_3 := h2079c.2.2.2
                linarith only [hlam, p2079_0]
          · linarith only [h2076, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2106 | h2106
        · linarith only [h2106, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2108 | h2108
          · rcases p0_3 (m.d 0 5) (by simp) with h2109 | h2109
            · linarith only [h2073, h2109, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hlam, p2111_0]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [h2109, hc15, hlam, hphi, ht0b, ht5b, p0_1, p2111_1, u0elo3]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [h2072, h2109, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2111_1, u1elo0]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [h2072, h2109, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2111_1, u1elo0]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [h2072, h2109, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2111_1, u1elo0]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc05, hlam, hphi, p2111_1, u5elo1]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hlam, p2111_0]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc25, hlam, hphi, p2111_1, u5elo1]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc35, hlam, hphi, p2111_1, u5elo1]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc45, hlam, hphi, p2111_1, u5elo1]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc05, hlam, hphi, p2111_1, u5elo2]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc15, hlam, hphi, p2111_1, u5elo2]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hlam, p2111_0]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc35, hlam, hphi, p2111_1, u5elo2]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc45, hlam, hphi, p2111_1, u5elo2]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc05, hlam, hphi, p2111_1, u5elo3]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc15, hlam, hphi, p2111_1, u5elo3]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc25, hlam, hphi, p2111_1, u5elo3]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hlam, p2111_0]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc45, hlam, hphi, p2111_1, u5elo3]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc05, hlam, hphi, p2111_1, u5elo4]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc15, hlam, hphi, p2111_1, u5elo4]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc25, hlam, hphi, p2111_1, u5elo4]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hc35, hlam, hphi, p2111_1, u5elo4]
              · have p2111_0 := h2111c.1
                have p2111_1 := h2111c.2.1
                have p2111_2 := h2111c.2.2.1
                have p2111_3 := h2111c.2.2.2
                linarith only [hlam, p2111_0]
          · linarith only [h2108, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2138 | h2138
      · rcases p0_3 (m.d 0 3) (by simp) with h2139 | h2139
        · linarith only [h2139, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2141 | h2141
          · rcases p0_3 (m.d 0 5) (by simp) with h2142 | h2142
            · linarith only [h2072, h2142, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hlam, p2144_0]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [h2138, h2142, hc15, hlam, hphi, ht0b, ht5b, p0_1, p2144_1, u0elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [h2138, h2142, hc25, hlam, hphi, ht0b, ht5b, p0_1, p2144_1, u0elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [h2138, h2142, hc35, hlam, hphi, ht0b, ht5b, p0_1, p2144_1, u0elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [h2138, h2142, hc45, hlam, hphi, ht0b, ht5b, p0_1, p2144_1, u0elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc05, hlam, hphi, p2144_1, u5elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hlam, p2144_0]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc25, hlam, hphi, p2144_1, u5elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc35, hlam, hphi, p2144_1, u5elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc45, hlam, hphi, p2144_1, u5elo1]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc05, hlam, hphi, p2144_1, u5elo2]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc15, hlam, hphi, p2144_1, u5elo2]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hlam, p2144_0]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc35, hlam, hphi, p2144_1, u5elo2]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc45, hlam, hphi, p2144_1, u5elo2]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc05, hlam, hphi, p2144_1, u5elo3]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc15, hlam, hphi, p2144_1, u5elo3]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc25, hlam, hphi, p2144_1, u5elo3]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hlam, p2144_0]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc45, hlam, hphi, p2144_1, u5elo3]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc05, hlam, hphi, p2144_1, u5elo4]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc15, hlam, hphi, p2144_1, u5elo4]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc25, hlam, hphi, p2144_1, u5elo4]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hc35, hlam, hphi, p2144_1, u5elo4]
              · have p2144_0 := h2144c.1
                have p2144_1 := h2144c.2.1
                have p2144_2 := h2144c.2.2.1
                have p2144_3 := h2144c.2.2.2
                linarith only [hlam, p2144_0]
          · linarith only [h2141, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2171 | h2171
        · linarith only [h2171, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2173 | h2173
          · rcases p0_3 (m.d 0 5) (by simp) with h2174 | h2174
            · linarith only [h2138, h2174, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h5bigk with h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hlam, p2176_0]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [h2174, hc15, hlam, hphi, ht0b, ht5b, p0_1, p2176_1, u0elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [h2174, hc25, hlam, hphi, ht0b, ht5b, p0_1, p2176_1, u0elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [h2174, hc35, hlam, hphi, ht0b, ht5b, p0_1, p2176_1, u0elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [h2174, hc45, hlam, hphi, ht0b, ht5b, p0_1, p2176_1, u0elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc05, hlam, hphi, p2176_1, u5elo1]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hlam, p2176_0]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc25, hlam, hphi, p2176_1, u5elo1]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc35, hlam, hphi, p2176_1, u5elo1]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc45, hlam, hphi, p2176_1, u5elo1]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc05, hlam, hphi, p2176_1, u5elo2]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc15, hlam, hphi, p2176_1, u5elo2]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hlam, p2176_0]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc35, hlam, hphi, p2176_1, u5elo2]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc45, hlam, hphi, p2176_1, u5elo2]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc05, hlam, hphi, p2176_1, u5elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc15, hlam, hphi, p2176_1, u5elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc25, hlam, hphi, p2176_1, u5elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hlam, p2176_0]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc45, hlam, hphi, p2176_1, u5elo3]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc05, hlam, hphi, p2176_1, u5elo4]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc15, hlam, hphi, p2176_1, u5elo4]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc25, hlam, hphi, p2176_1, u5elo4]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hc35, hlam, hphi, p2176_1, u5elo4]
              · have p2176_0 := h2176c.1
                have p2176_1 := h2176c.2.1
                have p2176_2 := h2176c.2.2.1
                have p2176_3 := h2176c.2.2.2
                linarith only [hlam, p2176_0]
          · linarith only [h2173, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2204 | h2204
    · rcases p0_3 (m.d 0 2) (by simp) with h2205 | h2205
      · rcases p0_3 (m.d 0 3) (by simp) with h2206 | h2206
        · rcases p0_3 (m.d 0 4) (by simp) with h2207 | h2207
          · rcases p0_3 (m.d 0 5) (by simp) with h2208 | h2208
            · linarith only [h2208, hlam, p0_0]
            · rcases h5bigk with h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hlam, p2210_0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc15, hlam, hphi, p2210_1, u5elo0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [h2204, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2210_1, u1elo0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [h2204, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2210_1, u1elo0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [h2204, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2210_1, u1elo0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc05, hlam, hphi, p2210_1, u5elo1]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hlam, p2210_0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc25, hlam, hphi, p2210_1, u5elo1]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc35, hlam, hphi, p2210_1, u5elo1]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc45, hlam, hphi, p2210_1, u5elo1]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc05, hlam, hphi, p2210_1, u5elo2]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc15, hlam, hphi, p2210_1, u5elo2]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hlam, p2210_0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc35, hlam, hphi, p2210_1, u5elo2]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc45, hlam, hphi, p2210_1, u5elo2]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc05, hlam, hphi, p2210_1, u5elo3]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc15, hlam, hphi, p2210_1, u5elo3]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc25, hlam, hphi, p2210_1, u5elo3]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hlam, p2210_0]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc45, hlam, hphi, p2210_1, u5elo3]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc05, hlam, hphi, p2210_1, u5elo4]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc15, hlam, hphi, p2210_1, u5elo4]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc25, hlam, hphi, p2210_1, u5elo4]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hc35, hlam, hphi, p2210_1, u5elo4]
              · have p2210_0 := h2210c.1
                have p2210_1 := h2210c.2.1
                have p2210_2 := h2210c.2.2.1
                have p2210_3 := h2210c.2.2.2
                linarith only [hlam, p2210_0]
          · linarith only [h2207, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2237 | h2237
          · rcases p0_3 (m.d 0 5) (by simp) with h2238 | h2238
            · linarith only [h2238, hlam, p0_0]
            · rcases h5bigk with h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hlam, p2240_0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc15, hlam, hphi, p2240_1, u5elo0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [h2204, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2240_1, u1elo0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [h2204, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2240_1, u1elo0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [h2204, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2240_1, u1elo0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc05, hlam, hphi, p2240_1, u5elo1]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hlam, p2240_0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc25, hlam, hphi, p2240_1, u5elo1]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc35, hlam, hphi, p2240_1, u5elo1]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc45, hlam, hphi, p2240_1, u5elo1]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [h2206, hc03, hlam, hphi, ht34, ht45, p2240_1, u5elo2]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc15, hlam, hphi, p2240_1, u5elo2]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hlam, p2240_0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc35, hlam, hphi, p2240_1, u5elo2]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc45, hlam, hphi, p2240_1, u5elo2]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [h2206, hc03, hlam, hphi, ht34, ht45, p2240_1, u5elo3]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc15, hlam, hphi, p2240_1, u5elo3]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc25, hlam, hphi, p2240_1, u5elo3]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hlam, p2240_0]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc45, hlam, hphi, p2240_1, u5elo3]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [h2206, hc03, hlam, hphi, ht34, ht45, p2240_1, u5elo4]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc15, hlam, hphi, p2240_1, u5elo4]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc25, hlam, hphi, p2240_1, u5elo4]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hc35, hlam, hphi, p2240_1, u5elo4]
              · have p2240_0 := h2240c.1
                have p2240_1 := h2240c.2.1
                have p2240_2 := h2240c.2.2.1
                have p2240_3 := h2240c.2.2.2
                linarith only [hlam, p2240_0]
          · linarith only [h2237, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2267 | h2267
        · rcases p0_3 (m.d 0 4) (by simp) with h2268 | h2268
          · rcases p0_3 (m.d 0 5) (by simp) with h2269 | h2269
            · linarith only [h2269, hlam, p0_0]
            · rcases h5bigk with h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hlam, p2271_0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc15, hlam, hphi, p2271_1, u5elo0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [h2204, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2271_1, u1elo0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [h2204, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2271_1, u1elo0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [h2204, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2271_1, u1elo0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc05, hlam, hphi, p2271_1, u5elo1]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hlam, p2271_0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc25, hlam, hphi, p2271_1, u5elo1]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc35, hlam, hphi, p2271_1, u5elo1]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc45, hlam, hphi, p2271_1, u5elo1]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [h2205, hc02, hlam, hphi, ht23, ht34, ht45, p2271_1, u5elo2]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc15, hlam, hphi, p2271_1, u5elo2]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hlam, p2271_0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc35, hlam, hphi, p2271_1, u5elo2]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc45, hlam, hphi, p2271_1, u5elo2]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [h2205, hc02, hlam, hphi, ht23, ht34, ht45, p2271_1, u5elo3]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc15, hlam, hphi, p2271_1, u5elo3]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc25, hlam, hphi, p2271_1, u5elo3]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hlam, p2271_0]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc45, hlam, hphi, p2271_1, u5elo3]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [h2205, hc02, hlam, hphi, ht23, ht34, ht45, p2271_1, u5elo4]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc15, hlam, hphi, p2271_1, u5elo4]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc25, hlam, hphi, p2271_1, u5elo4]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hc35, hlam, hphi, p2271_1, u5elo4]
              · have p2271_0 := h2271c.1
                have p2271_1 := h2271c.2.1
                have p2271_2 := h2271c.2.2.1
                have p2271_3 := h2271c.2.2.2
                linarith only [hlam, p2271_0]
          · linarith only [h2268, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2298 | h2298
          · rcases p0_3 (m.d 0 5) (by simp) with h2299 | h2299
            · linarith only [h2299, hlam, p0_0]
            · rcases h5bigk with h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hlam, p2301_0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc15, hlam, hphi, p2301_1, u5elo0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [h2204, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2301_1, u1elo0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [h2204, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2301_1, u1elo0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [h2204, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, p2301_1, u1elo0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [h2267, hc03, hlam, hphi, ht34, ht45, p2301_1, u5elo1]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hlam, p2301_0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc25, hlam, hphi, p2301_1, u5elo1]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc35, hlam, hphi, p2301_1, u5elo1]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc45, hlam, hphi, p2301_1, u5elo1]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [h2205, hc02, hlam, hphi, ht23, ht34, ht45, p2301_1, u5elo2]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc15, hlam, hphi, p2301_1, u5elo2]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hlam, p2301_0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc35, hlam, hphi, p2301_1, u5elo2]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc45, hlam, hphi, p2301_1, u5elo2]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [h2205, hc02, hlam, hphi, ht23, ht34, ht45, p2301_1, u5elo3]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc15, hlam, hphi, p2301_1, u5elo3]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc25, hlam, hphi, p2301_1, u5elo3]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hlam, p2301_0]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc45, hlam, hphi, p2301_1, u5elo3]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [h2205, hc02, hlam, hphi, ht23, ht34, ht45, p2301_1, u5elo4]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc15, hlam, hphi, p2301_1, u5elo4]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc25, hlam, hphi, p2301_1, u5elo4]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hc35, hlam, hphi, p2301_1, u5elo4]
              · have p2301_0 := h2301c.1
                have p2301_1 := h2301c.2.1
                have p2301_2 := h2301c.2.2.1
                have p2301_3 := h2301c.2.2.2
                linarith only [hlam, p2301_0]
          · linarith only [h2298, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2328 | h2328
      · rcases p0_3 (m.d 0 3) (by simp) with h2329 | h2329
        · rcases p0_3 (m.d 0 4) (by simp) with h2330 | h2330
          · rcases p0_3 (m.d 0 5) (by simp) with h2331 | h2331
            · linarith only [h2331, hlam, p0_0]
            · rcases h5bigk with h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c | h2333c
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hlam, p2333_0]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [h2328, hc15, hlam, hphi, ht0b, ht5b, p0_1, p2333_1, u0elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [h2328, hc25, hlam, hphi, ht0b, ht5b, p0_1, p2333_1, u0elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [h2328, hc35, hlam, hphi, ht0b, ht5b, p0_1, p2333_1, u0elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [h2328, hc45, hlam, hphi, ht0b, ht5b, p0_1, p2333_1, u0elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc05, hlam, hphi, p2333_1, u5elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hlam, p2333_0]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc25, hlam, hphi, p2333_1, u5elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc35, hlam, hphi, p2333_1, u5elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc45, hlam, hphi, p2333_1, u5elo1]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2333_1, u5elo2]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc15, hlam, hphi, p2333_1, u5elo2]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hlam, p2333_0]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc35, hlam, hphi, p2333_1, u5elo2]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc45, hlam, hphi, p2333_1, u5elo2]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2333_1, u5elo3]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc15, hlam, hphi, p2333_1, u5elo3]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc25, hlam, hphi, p2333_1, u5elo3]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hlam, p2333_0]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc45, hlam, hphi, p2333_1, u5elo3]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2333_1, u5elo4]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc15, hlam, hphi, p2333_1, u5elo4]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc25, hlam, hphi, p2333_1, u5elo4]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hc35, hlam, hphi, p2333_1, u5elo4]
              · have p2333_0 := h2333c.1
                have p2333_1 := h2333c.2.1
                have p2333_2 := h2333c.2.2.1
                have p2333_3 := h2333c.2.2.2
                linarith only [hlam, p2333_0]
          · linarith only [h2330, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2360 | h2360
          · rcases p0_3 (m.d 0 5) (by simp) with h2361 | h2361
            · linarith only [h2361, hlam, p0_0]
            · rcases h5bigk with h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hlam, p2363_0]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc15, hlam, hphi, p2363_1, u5elo0]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [h2328, hc25, hlam, hphi, ht0b, ht5b, p0_1, p2363_1, u0elo1]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [h2328, hc35, hlam, hphi, ht0b, ht5b, p0_1, p2363_1, u0elo1]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [h2328, hc45, hlam, hphi, ht0b, ht5b, p0_1, p2363_1, u0elo1]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [h2329, hc03, hlam, hphi, ht34, ht45, p2363_1, u5elo1]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hlam, p2363_0]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc25, hlam, hphi, p2363_1, u5elo1]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc35, hlam, hphi, p2363_1, u5elo1]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc45, hlam, hphi, p2363_1, u5elo1]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2363_1, u5elo2]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc15, hlam, hphi, p2363_1, u5elo2]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hlam, p2363_0]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc35, hlam, hphi, p2363_1, u5elo2]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc45, hlam, hphi, p2363_1, u5elo2]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2363_1, u5elo3]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc15, hlam, hphi, p2363_1, u5elo3]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc25, hlam, hphi, p2363_1, u5elo3]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hlam, p2363_0]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc45, hlam, hphi, p2363_1, u5elo3]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2363_1, u5elo4]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc15, hlam, hphi, p2363_1, u5elo4]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc25, hlam, hphi, p2363_1, u5elo4]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hc35, hlam, hphi, p2363_1, u5elo4]
              · have p2363_0 := h2363c.1
                have p2363_1 := h2363c.2.1
                have p2363_2 := h2363c.2.2.1
                have p2363_3 := h2363c.2.2.2
                linarith only [hlam, p2363_0]
          · linarith only [h2360, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2390 | h2390
        · rcases p0_3 (m.d 0 4) (by simp) with h2391 | h2391
          · rcases p0_3 (m.d 0 5) (by simp) with h2392 | h2392
            · linarith only [h2392, hlam, p0_0]
            · rcases h5bigk with h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hlam, p2394_0]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc15, hlam, hphi, p2394_1, u5elo0]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p2394_1, u0elo3]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p2394_1, u0elo3]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p2394_1, u0elo3]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [h2328, hc02, hlam, hphi, ht23, ht34, ht45, p2394_1, u5elo1]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hlam, p2394_0]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc25, hlam, hphi, p2394_1, u5elo1]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc35, hlam, hphi, p2394_1, u5elo1]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc45, hlam, hphi, p2394_1, u5elo1]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2394_1, u5elo2]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc15, hlam, hphi, p2394_1, u5elo2]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hlam, p2394_0]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc35, hlam, hphi, p2394_1, u5elo2]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc45, hlam, hphi, p2394_1, u5elo2]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2394_1, u5elo3]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc15, hlam, hphi, p2394_1, u5elo3]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc25, hlam, hphi, p2394_1, u5elo3]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hlam, p2394_0]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc45, hlam, hphi, p2394_1, u5elo3]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2394_1, u5elo4]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc15, hlam, hphi, p2394_1, u5elo4]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc25, hlam, hphi, p2394_1, u5elo4]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hc35, hlam, hphi, p2394_1, u5elo4]
              · have p2394_0 := h2394c.1
                have p2394_1 := h2394c.2.1
                have p2394_2 := h2394c.2.2.1
                have p2394_3 := h2394c.2.2.2
                linarith only [hlam, p2394_0]
          · linarith only [h2391, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2421 | h2421
          · rcases p0_3 (m.d 0 5) (by simp) with h2422 | h2422
            · linarith only [h2422, hlam, p0_0]
            · rcases h5bigk with h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c | h2424c
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hlam, p2424_0]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc15, hlam, hphi, p2424_1, u5elo0]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, p2424_1, u0elo3]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, p2424_1, u0elo3]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, p2424_1, u0elo3]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [h2390, hc03, hlam, hphi, ht34, ht45, p2424_1, u5elo1]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hlam, p2424_0]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc25, hlam, hphi, p2424_1, u5elo1]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc35, hlam, hphi, p2424_1, u5elo1]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc45, hlam, hphi, p2424_1, u5elo1]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2424_1, u5elo2]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc15, hlam, hphi, p2424_1, u5elo2]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hlam, p2424_0]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc35, hlam, hphi, p2424_1, u5elo2]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc45, hlam, hphi, p2424_1, u5elo2]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2424_1, u5elo3]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc15, hlam, hphi, p2424_1, u5elo3]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc25, hlam, hphi, p2424_1, u5elo3]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hlam, p2424_0]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc45, hlam, hphi, p2424_1, u5elo3]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [h2204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2424_1, u5elo4]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc15, hlam, hphi, p2424_1, u5elo4]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc25, hlam, hphi, p2424_1, u5elo4]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hc35, hlam, hphi, p2424_1, u5elo4]
              · have p2424_0 := h2424c.1
                have p2424_1 := h2424c.2.1
                have p2424_2 := h2424c.2.2.1
                have p2424_3 := h2424c.2.2.2
                linarith only [hlam, p2424_0]
          · linarith only [h2421, hlam, p0_0]
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

end R2N4
