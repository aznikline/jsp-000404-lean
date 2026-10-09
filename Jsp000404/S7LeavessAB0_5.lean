import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB0_H_I_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h0elo := hb0.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
              · linarith only [h13, hlam, p0_0]
              · linarith only [h13, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h16 | h16
            · linarith only [h16, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h18 | h18
              · linarith only [h18, hlam, p0_0]
              · linarith only [h18, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · linarith only [h22, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
              · linarith only [h24, hlam, p0_0]
              · linarith only [h24, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · linarith only [h27, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
              · linarith only [h29, hlam, p0_0]
              · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · linarith only [h34, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h36 | h36
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · linarith only [h37, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h39 | h39
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
              · linarith only [h42, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h34, h42, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h34, h45, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h47 | h47
              · linarith only [h34, h47, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h34, h47, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h36, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h51 | h51
    · linarith only [h51, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
      · rcases p0_3 (m.d 2 4) (by simp) with h54 | h54
        · rcases p0_3 (m.d 3 4) (by simp) with h55 | h55
          · linarith only [h55, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h59 | h59
              · linarith only [h59, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h51, h59, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h62 | h62
          · linarith only [h62, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · linarith only [h51, h64, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
              · linarith only [h51, h66, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h51, h66, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h53, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · linarith only [h70, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h72 | h72
      · rcases p0_3 (m.d 2 4) (by simp) with h73 | h73
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
              · linarith only [h70, h77, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h77, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h82 | h82
              · linarith only [h70, h82, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h82, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h85 | h85
          · rcases p0_3 (m.d 4 5) (by simp) with h86 | h86
            · linarith only [h86, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
              · linarith only [h70, h88, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h88, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h91 | h91
            · linarith only [h91, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h93 | h93
              · linarith only [h70, h93, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h93, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h72, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h97 | h97
    · linarith only [h97, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h99 | h99
      · rcases p0_3 (m.d 2 4) (by simp) with h100 | h100
        · rcases p0_3 (m.d 3 4) (by simp) with h101 | h101
          · rcases p0_3 (m.d 4 5) (by simp) with h102 | h102
            · linarith only [h102, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h104 | h104
              · linarith only [h104, h99, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h104, h99, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h109 | h109
              · linarith only [h109, h99, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h109, h99, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h100, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · rcases p0_3 (m.d 4 5) (by simp) with h115 | h115
            · linarith only [h115, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h117 | h117
              · rcases m.htr 0 2 4 (by decide) (by decide) with h118 | h118
                · linarith only [h118, hlam, p0_0]
                · linarith only [h114, h118, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h117, h99, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h124 | h124
              · rcases m.htr 0 2 4 (by decide) (by decide) with h125 | h125
                · linarith only [h125, hlam, p0_0]
                · linarith only [h125, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h124, h99, hlam]
        · linarith only [h113, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h130 | h130
    · linarith only [h130, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h132 | h132
      · linarith only [h132, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h134 | h134
        · rcases p0_3 (m.d 3 4) (by simp) with h135 | h135
          · rcases p0_3 (m.d 4 5) (by simp) with h136 | h136
            · linarith only [h136, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
              · linarith only [h130, h138, hlam]
              · linarith only [h135, h138, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h141 | h141
            · linarith only [h141, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h143 | h143
              · linarith only [h130, h143, hlam]
              · linarith only [h143, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h134, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · linarith only [h148, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · linarith only [h152, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h154 | h154
            · linarith only [h154, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h156 | h156
              · linarith only [h150, h156, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h148, h150, h156, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h151, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h160 | h160
        · rcases p0_3 (m.d 3 4) (by simp) with h161 | h161
          · linarith only [h161, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h163 | h163
            · linarith only [h148, h163, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h165 | h165
              · rcases m.htr 0 2 4 (by decide) (by decide) with h166 | h166
                · linarith only [h148, h165, h166, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h148, h166, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h150, h165, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h160, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h171 | h171
    · linarith only [h171, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h173 | h173
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h176, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h178 | h178
              · linarith only [h171, h173, h178, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h171, h173, h178, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h181 | h181
            · linarith only [h181, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h183 | h183
              · linarith only [h171, h173, h183, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h171, h173, h183, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h174, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h187 | h187
        · rcases p0_3 (m.d 3 4) (by simp) with h188 | h188
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h191 | h191
              · rcases m.htr 0 2 4 (by decide) (by decide) with h192 | h192
                · linarith only [h171, h191, h192, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h171, h188, h192, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h173, h188, h191, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h196, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h198 | h198
              · rcases m.htr 0 2 4 (by decide) (by decide) with h199 | h199
                · linarith only [h171, h198, h199, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h171, h199, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h173, h198, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h187, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h204 | h204
    · linarith only [h204, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h206 | h206
      · rcases p0_3 (m.d 2 4) (by simp) with h207 | h207
        · rcases p0_3 (m.d 3 4) (by simp) with h208 | h208
          · rcases p0_3 (m.d 4 5) (by simp) with h209 | h209
            · linarith only [h209, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
              · linarith only [h206, h211, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h206, h211, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h208, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h215 | h215
          · rcases p0_3 (m.d 4 5) (by simp) with h216 | h216
            · linarith only [h216, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h218 | h218
              · linarith only [h206, h218, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h206, h218, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h215, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h222 | h222
        · rcases p0_3 (m.d 3 4) (by simp) with h223 | h223
          · rcases p0_3 (m.d 4 5) (by simp) with h224 | h224
            · linarith only [h224, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 2 4 (by decide) (by decide) with h227 | h227
                · linarith only [h222, h226, h227, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h227, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h206, h226, hlam]
          · linarith only [h223, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h232 | h232
          · rcases p0_3 (m.d 4 5) (by simp) with h233 | h233
            · linarith only [h233, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h235 | h235
              · rcases m.htr 0 2 4 (by decide) (by decide) with h236 | h236
                · rcases m.htr 0 3 4 (by decide) (by decide) with h237 | h237
                  · linarith only [h237, hlam, p0_0]
                  · linarith only [h237, hc03, hc34, hlam, hphi, p0_1]
                · linarith only [h222, h236, hlam]
              · linarith only [h206, h235, hlam]
          · linarith only [h232, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h243 | h243
    · linarith only [h243, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h245 | h245
      · linarith only [h245, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h247 | h247
        · rcases p0_3 (m.d 3 4) (by simp) with h248 | h248
          · rcases p0_3 (m.d 4 5) (by simp) with h249 | h249
            · linarith only [h249, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h251 | h251
              · linarith only [h243, h251, hlam]
              · linarith only [h247, h251, hc01, hc24, hlam, hphi, ht12, p0_1]
          · linarith only [h248, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h255 | h255
          · rcases p0_3 (m.d 4 5) (by simp) with h256 | h256
            · linarith only [h256, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h258 | h258
              · linarith only [h243, h258, hlam]
              · linarith only [h258, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h255, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h262 | h262
    · linarith only [h262, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h264 | h264
      · rcases p0_3 (m.d 2 4) (by simp) with h265 | h265
        · linarith only [h265, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h267 | h267
          · rcases p0_3 (m.d 4 5) (by simp) with h268 | h268
            · linarith only [h268, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h270 | h270
              · linarith only [h264, h270, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h262, h264, h270, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h267, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h274 | h274
        · linarith only [h274, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h276 | h276
          · rcases p0_3 (m.d 4 5) (by simp) with h277 | h277
            · linarith only [h262, h277, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h279 | h279
              · rcases m.htr 0 2 4 (by decide) (by decide) with h280 | h280
                · linarith only [h262, h280, hlam]
                · linarith only [h280, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h264, h279, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h276, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h286 | h286
    · linarith only [h286, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h288 | h288
      · rcases p0_3 (m.d 2 4) (by simp) with h289 | h289
        · rcases p0_3 (m.d 3 4) (by simp) with h290 | h290
          · rcases p0_3 (m.d 4 5) (by simp) with h291 | h291
            · linarith only [h291, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h293 | h293
              · linarith only [h286, h288, h293, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h286, h288, h293, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h290, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h297 | h297
          · rcases p0_3 (m.d 4 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h300 | h300
              · linarith only [h286, h288, h300, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h286, h288, h300, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h297, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h304 | h304
        · rcases p0_3 (m.d 3 4) (by simp) with h305 | h305
          · rcases p0_3 (m.d 4 5) (by simp) with h306 | h306
            · linarith only [h306, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
                · linarith only [h286, h304, h308, h309, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h286, h309, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h288, h308, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h305, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h314 | h314
          · rcases p0_3 (m.d 4 5) (by simp) with h315 | h315
            · linarith only [h315, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h286, h317, h319, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2]
                  · linarith only [h286, h319, hc03, hc34, hlam, hphi, p0_1]
                · linarith only [h304, h318, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h288, h317, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h314, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h0elo := hb0.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
              · linarith only [h13, hlam, p0_0]
              · linarith only [h13, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h16 | h16
            · linarith only [h16, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h18 | h18
              · linarith only [h18, hlam, p0_0]
              · linarith only [h18, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · linarith only [h22, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
              · linarith only [h24, hlam, p0_0]
              · linarith only [h24, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · linarith only [h27, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
              · linarith only [h29, hlam, p0_0]
              · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · linarith only [h34, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h36 | h36
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · linarith only [h37, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h39 | h39
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
              · linarith only [h42, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h34, h42, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h34, h45, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h47 | h47
              · linarith only [h34, h47, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h34, h47, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h36, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h51 | h51
    · linarith only [h51, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
      · rcases p0_3 (m.d 2 4) (by simp) with h54 | h54
        · rcases p0_3 (m.d 3 4) (by simp) with h55 | h55
          · linarith only [h55, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h59 | h59
              · linarith only [h59, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h51, h59, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h62 | h62
          · linarith only [h62, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · linarith only [h51, h64, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
              · linarith only [h51, h66, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h51, h66, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h53, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · linarith only [h70, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h72 | h72
      · rcases p0_3 (m.d 2 4) (by simp) with h73 | h73
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
              · linarith only [h70, h77, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h77, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h82 | h82
              · linarith only [h70, h82, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h82, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h85 | h85
          · rcases p0_3 (m.d 4 5) (by simp) with h86 | h86
            · linarith only [h86, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
              · linarith only [h70, h88, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h88, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h91 | h91
            · linarith only [h91, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h93 | h93
              · linarith only [h70, h93, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h70, h93, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h72, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h97 | h97
    · linarith only [h97, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h99 | h99
      · rcases p0_3 (m.d 2 4) (by simp) with h100 | h100
        · rcases p0_3 (m.d 3 4) (by simp) with h101 | h101
          · rcases p0_3 (m.d 4 5) (by simp) with h102 | h102
            · linarith only [h102, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h104 | h104
              · linarith only [h104, h99, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h104, h99, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h109 | h109
              · linarith only [h109, h99, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h109, h99, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h100, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · rcases p0_3 (m.d 4 5) (by simp) with h115 | h115
            · linarith only [h115, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h117 | h117
              · rcases m.htr 0 2 4 (by decide) (by decide) with h118 | h118
                · linarith only [h118, hlam, p0_0]
                · linarith only [h114, h118, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h117, h99, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h124 | h124
              · rcases m.htr 0 2 4 (by decide) (by decide) with h125 | h125
                · linarith only [h125, hlam, p0_0]
                · linarith only [h125, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h124, h99, hlam]
        · linarith only [h113, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h130 | h130
    · linarith only [h130, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h132 | h132
      · linarith only [h132, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h134 | h134
        · rcases p0_3 (m.d 3 4) (by simp) with h135 | h135
          · rcases p0_3 (m.d 4 5) (by simp) with h136 | h136
            · linarith only [h136, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
              · linarith only [h130, h138, hlam]
              · linarith only [h138, hc01, hc24, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h141 | h141
            · linarith only [h141, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h143 | h143
              · linarith only [h130, h143, hlam]
              · linarith only [h143, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h134, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · linarith only [h148, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · linarith only [h152, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h154 | h154
            · linarith only [h154, hc34, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h156 | h156
              · linarith only [h150, h156, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h148, h150, h156, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h151, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h160 | h160
        · rcases p0_3 (m.d 3 4) (by simp) with h161 | h161
          · linarith only [h161, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h163 | h163
            · linarith only [h148, h163, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h165 | h165
              · rcases m.htr 0 2 4 (by decide) (by decide) with h166 | h166
                · linarith only [h148, h165, h166, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h148, h166, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h150, h165, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h160, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h171 | h171
    · linarith only [h171, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h173 | h173
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h176, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h178 | h178
              · linarith only [h171, h173, h178, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h171, h173, h178, hc01, hc14, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h181 | h181
            · linarith only [h181, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h183 | h183
              · linarith only [h171, h173, h183, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h171, h173, h183, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h174, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h187 | h187
        · rcases p0_3 (m.d 3 4) (by simp) with h188 | h188
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h191 | h191
              · rcases m.htr 0 2 4 (by decide) (by decide) with h192 | h192
                · linarith only [h171, h191, h192, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h171, h188, h192, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h173, h188, h191, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h196, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h198 | h198
              · rcases m.htr 0 2 4 (by decide) (by decide) with h199 | h199
                · linarith only [h171, h198, h199, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h171, h199, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h173, h198, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h187, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h204 | h204
    · linarith only [h204, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h206 | h206
      · rcases p0_3 (m.d 2 4) (by simp) with h207 | h207
        · rcases p0_3 (m.d 3 4) (by simp) with h208 | h208
          · rcases p0_3 (m.d 4 5) (by simp) with h209 | h209
            · linarith only [h209, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
              · linarith only [h206, h211, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h206, h211, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h208, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h215 | h215
          · rcases p0_3 (m.d 4 5) (by simp) with h216 | h216
            · linarith only [h216, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h218 | h218
              · linarith only [h206, h218, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h206, h218, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h215, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h222 | h222
        · rcases p0_3 (m.d 3 4) (by simp) with h223 | h223
          · rcases p0_3 (m.d 4 5) (by simp) with h224 | h224
            · linarith only [h224, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h226 | h226
              · rcases m.htr 0 2 4 (by decide) (by decide) with h227 | h227
                · linarith only [h222, h226, h227, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h227, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h206, h226, hlam]
          · linarith only [h223, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h232 | h232
          · rcases p0_3 (m.d 4 5) (by simp) with h233 | h233
            · linarith only [h233, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h235 | h235
              · rcases m.htr 0 2 4 (by decide) (by decide) with h236 | h236
                · rcases m.htr 0 3 4 (by decide) (by decide) with h237 | h237
                  · linarith only [h237, hlam, p0_0]
                  · linarith only [h237, hc03, hc34, hlam, hphi, p0_1]
                · linarith only [h222, h236, hlam]
              · linarith only [h206, h235, hlam]
          · linarith only [h232, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h243 | h243
    · linarith only [h243, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h245 | h245
      · linarith only [h245, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h247 | h247
        · rcases p0_3 (m.d 3 4) (by simp) with h248 | h248
          · rcases p0_3 (m.d 4 5) (by simp) with h249 | h249
            · linarith only [h249, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h251 | h251
              · linarith only [h243, h251, hlam]
              · linarith only [h247, h251, hc01, hc24, hlam, hphi, ht12, p0_1]
          · linarith only [h248, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h255 | h255
          · rcases p0_3 (m.d 4 5) (by simp) with h256 | h256
            · linarith only [h256, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h258 | h258
              · linarith only [h243, h258, hlam]
              · linarith only [h258, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h255, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h262 | h262
    · linarith only [h262, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h264 | h264
      · rcases p0_3 (m.d 2 4) (by simp) with h265 | h265
        · linarith only [h265, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h267 | h267
          · rcases p0_3 (m.d 4 5) (by simp) with h268 | h268
            · linarith only [h268, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h270 | h270
              · linarith only [h264, h270, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h262, h264, h270, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h267, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h274 | h274
        · linarith only [h274, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h276 | h276
          · rcases p0_3 (m.d 4 5) (by simp) with h277 | h277
            · linarith only [h262, h277, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h279 | h279
              · rcases m.htr 0 2 4 (by decide) (by decide) with h280 | h280
                · linarith only [h262, h280, hlam]
                · linarith only [h280, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h264, h279, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h276, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h286 | h286
    · linarith only [h286, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h288 | h288
      · rcases p0_3 (m.d 2 4) (by simp) with h289 | h289
        · rcases p0_3 (m.d 3 4) (by simp) with h290 | h290
          · rcases p0_3 (m.d 4 5) (by simp) with h291 | h291
            · linarith only [h291, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h293 | h293
              · linarith only [h286, h288, h293, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h286, h288, h293, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h290, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h297 | h297
          · rcases p0_3 (m.d 4 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h300 | h300
              · linarith only [h286, h288, h300, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h286, h288, h300, hc01, hc14, hlam, hphi, p0_1]
          · linarith only [h297, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h304 | h304
        · rcases p0_3 (m.d 3 4) (by simp) with h305 | h305
          · rcases p0_3 (m.d 4 5) (by simp) with h306 | h306
            · linarith only [h306, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
                · linarith only [h286, h304, h308, h309, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1]
                · linarith only [h286, h309, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h288, h308, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h305, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h314 | h314
          · rcases p0_3 (m.d 4 5) (by simp) with h315 | h315
            · linarith only [h315, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h286, h317, h319, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2]
                  · linarith only [h286, h319, hc03, hc34, hlam, hphi, p0_1]
                · linarith only [h304, h318, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h288, h317, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h314, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have h0elo := hb0.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 4 5) (by simp) with h18 | h18
            · linarith only [h18, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h18, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h21, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h26 | h26
    · linarith only [h26, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h28 | h28
      · rcases p0_3 (m.d 2 4) (by simp) with h29 | h29
        · linarith only [h29, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h31 | h31
          · rcases p0_3 (m.d 4 5) (by simp) with h32 | h32
            · linarith only [h32, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h32, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h26, h35, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h28, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h39 | h39
    · linarith only [h39, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h41 | h41
      · rcases p0_3 (m.d 2 4) (by simp) with h42 | h42
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h45, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h45, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h48 | h48
          · linarith only [h48, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h50 | h50
            · linarith only [h39, h50, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h50, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h41, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · rcases p0_3 (m.d 2 4) (by simp) with h58 | h58
        · rcases p0_3 (m.d 3 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h58, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h67 | h67
        · rcases p0_3 (m.d 3 4) (by simp) with h68 | h68
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · linarith only [h69, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h69, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h72 | h72
            · linarith only [h72, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h72, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h67, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
    · linarith only [h76, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h78 | h78
      · linarith only [h78, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h80 | h80
        · rcases p0_3 (m.d 3 4) (by simp) with h81 | h81
          · rcases p0_3 (m.d 4 5) (by simp) with h82 | h82
            · linarith only [h82, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h82, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h76, h85, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h80, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · linarith only [h90, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · linarith only [h94, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h92, h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h93, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h100 | h100
        · rcases p0_3 (m.d 3 4) (by simp) with h101 | h101
          · linarith only [h101, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h103 | h103
            · linarith only [h103, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h103, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h108 | h108
    · linarith only [h108, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h110 | h110
      · rcases p0_3 (m.d 2 4) (by simp) with h111 | h111
        · rcases p0_3 (m.d 3 4) (by simp) with h112 | h112
          · rcases p0_3 (m.d 4 5) (by simp) with h113 | h113
            · linarith only [h113, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h110, h113, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h112, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h117, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h122 | h122
        · rcases p0_3 (m.d 3 4) (by simp) with h123 | h123
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h122, h124, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h123, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h128, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · linarith only [h133, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h135 | h135
      · linarith only [h135, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h137 | h137
        · rcases p0_3 (m.d 3 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 4 5) (by simp) with h139 | h139
            · linarith only [h139, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, h139, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h138, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h133, h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h143, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · linarith only [h148, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · linarith only [h151, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h153 | h153
          · rcases p0_3 (m.d 4 5) (by simp) with h154 | h154
            · linarith only [h154, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h150, h154, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h153, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h158 | h158
        · linarith only [h158, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h160 | h160
          · rcases p0_3 (m.d 4 5) (by simp) with h161 | h161
            · linarith only [h148, h161, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h161, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h160, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h70, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h125, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h160, h179, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h174, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h208, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h236, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h263, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h294, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have h0ehi := hb0.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h70, h75, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · linarith only [h78, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h78, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 4) (by simp) with h84 | h84
      · rcases p0_3 (m.d 2 4) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · linarith only [h88, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h83, h88, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h85, h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h84, hlam, p0_0]
    · linarith only [h83, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h100 | h100
    · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
      · linarith only [h101, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h103 | h103
        · rcases p0_3 (m.d 3 4) (by simp) with h104 | h104
          · rcases p0_3 (m.d 4 5) (by simp) with h105 | h105
            · linarith only [h105, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h100, h105, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h103, hlam, p0_0]
    · linarith only [h100, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h119, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h123, hlam, p0_0]
    · linarith only [h114, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · rcases p0_3 (m.d 3 4) (by simp) with h137 | h137
          · rcases p0_3 (m.d 4 5) (by simp) with h138 | h138
            · linarith only [h138, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h133, h138, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h137, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h143, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h142, hlam, p0_0]
    · linarith only [h133, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 4) (by simp) with h149 | h149
      · rcases p0_3 (m.d 2 4) (by simp) with h150 | h150
        · linarith only [h150, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h148, h153, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h152, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h149, h160, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
    · linarith only [h148, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h0elo := hb0.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 4 5) (by simp) with h18 | h18
            · linarith only [h18, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h18, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h21, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h26 | h26
    · linarith only [h26, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h28 | h28
      · rcases p0_3 (m.d 2 4) (by simp) with h29 | h29
        · linarith only [h29, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h31 | h31
          · rcases p0_3 (m.d 4 5) (by simp) with h32 | h32
            · linarith only [h32, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h32, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h26, h35, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h28, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h39 | h39
    · linarith only [h39, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h41 | h41
      · rcases p0_3 (m.d 2 4) (by simp) with h42 | h42
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h45, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h45, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h48 | h48
          · linarith only [h48, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h50 | h50
            · linarith only [h39, h50, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h50, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h41, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · rcases p0_3 (m.d 2 4) (by simp) with h58 | h58
        · rcases p0_3 (m.d 3 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h58, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h67 | h67
        · rcases p0_3 (m.d 3 4) (by simp) with h68 | h68
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · linarith only [h69, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h69, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h72 | h72
            · linarith only [h72, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h72, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h67, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
    · linarith only [h76, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h78 | h78
      · linarith only [h78, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h80 | h80
        · rcases p0_3 (m.d 3 4) (by simp) with h81 | h81
          · rcases p0_3 (m.d 4 5) (by simp) with h82 | h82
            · linarith only [h82, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h82, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h76, h85, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h80, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · linarith only [h90, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · linarith only [h94, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h92, h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h93, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h100 | h100
        · rcases p0_3 (m.d 3 4) (by simp) with h101 | h101
          · linarith only [h101, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h103 | h103
            · linarith only [h103, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h103, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h108 | h108
    · linarith only [h108, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h110 | h110
      · rcases p0_3 (m.d 2 4) (by simp) with h111 | h111
        · rcases p0_3 (m.d 3 4) (by simp) with h112 | h112
          · rcases p0_3 (m.d 4 5) (by simp) with h113 | h113
            · linarith only [h113, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h110, h113, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h112, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h117, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h122 | h122
        · rcases p0_3 (m.d 3 4) (by simp) with h123 | h123
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h122, h124, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h123, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h128, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · linarith only [h133, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h135 | h135
      · linarith only [h135, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h137 | h137
        · rcases p0_3 (m.d 3 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 4 5) (by simp) with h139 | h139
            · linarith only [h139, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, h139, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h138, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h133, h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h143, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · linarith only [h148, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · linarith only [h151, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h153 | h153
          · rcases p0_3 (m.d 4 5) (by simp) with h154 | h154
            · linarith only [h154, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h150, h154, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h153, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h158 | h158
        · linarith only [h158, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h160 | h160
          · rcases p0_3 (m.d 4 5) (by simp) with h161 | h161
            · linarith only [h148, h161, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h161, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h160, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h70, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h125, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h160, h179, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h174, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h208, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h236, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h263, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h294, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h0ehi := hb0.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h70, h75, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · linarith only [h78, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h78, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 4) (by simp) with h84 | h84
      · rcases p0_3 (m.d 2 4) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · linarith only [h88, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h83, h88, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h85, h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h84, hlam, p0_0]
    · linarith only [h83, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h100 | h100
    · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
      · linarith only [h101, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h103 | h103
        · rcases p0_3 (m.d 3 4) (by simp) with h104 | h104
          · rcases p0_3 (m.d 4 5) (by simp) with h105 | h105
            · linarith only [h105, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h100, h105, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h103, hlam, p0_0]
    · linarith only [h100, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h119, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h123, hlam, p0_0]
    · linarith only [h114, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · rcases p0_3 (m.d 3 4) (by simp) with h137 | h137
          · rcases p0_3 (m.d 4 5) (by simp) with h138 | h138
            · linarith only [h138, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h133, h138, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h137, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h143, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h142, hlam, p0_0]
    · linarith only [h133, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 4) (by simp) with h149 | h149
      · rcases p0_3 (m.d 2 4) (by simp) with h150 | h150
        · linarith only [h150, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h148, h153, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h152, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h149, h160, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
    · linarith only [h148, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h0elo := hb0.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 4 5) (by simp) with h18 | h18
            · linarith only [h18, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h18, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h21, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h26 | h26
    · linarith only [h26, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h28 | h28
      · rcases p0_3 (m.d 2 4) (by simp) with h29 | h29
        · linarith only [h29, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h31 | h31
          · rcases p0_3 (m.d 4 5) (by simp) with h32 | h32
            · linarith only [h32, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h32, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h26, h35, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h28, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h39 | h39
    · linarith only [h39, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h41 | h41
      · rcases p0_3 (m.d 2 4) (by simp) with h42 | h42
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h45, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h45, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h48 | h48
          · linarith only [h48, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h50 | h50
            · linarith only [h39, h50, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h50, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h41, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · rcases p0_3 (m.d 2 4) (by simp) with h58 | h58
        · rcases p0_3 (m.d 3 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h58, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h67 | h67
        · rcases p0_3 (m.d 3 4) (by simp) with h68 | h68
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · linarith only [h69, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h69, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h72 | h72
            · linarith only [h72, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h72, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h67, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
    · linarith only [h76, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h78 | h78
      · linarith only [h78, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h80 | h80
        · rcases p0_3 (m.d 3 4) (by simp) with h81 | h81
          · rcases p0_3 (m.d 4 5) (by simp) with h82 | h82
            · linarith only [h82, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h82, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h76, h85, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h80, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · linarith only [h90, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · linarith only [h94, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h92, h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h93, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h100 | h100
        · rcases p0_3 (m.d 3 4) (by simp) with h101 | h101
          · linarith only [h101, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h103 | h103
            · linarith only [h103, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h103, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h108 | h108
    · linarith only [h108, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h110 | h110
      · rcases p0_3 (m.d 2 4) (by simp) with h111 | h111
        · rcases p0_3 (m.d 3 4) (by simp) with h112 | h112
          · rcases p0_3 (m.d 4 5) (by simp) with h113 | h113
            · linarith only [h113, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h110, h113, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h112, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h117, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h122 | h122
        · rcases p0_3 (m.d 3 4) (by simp) with h123 | h123
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h122, h124, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h123, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h128, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · linarith only [h133, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h135 | h135
      · linarith only [h135, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h137 | h137
        · rcases p0_3 (m.d 3 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 4 5) (by simp) with h139 | h139
            · linarith only [h139, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, h139, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h138, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h133, h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h143, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · linarith only [h148, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · linarith only [h151, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h153 | h153
          · rcases p0_3 (m.d 4 5) (by simp) with h154 | h154
            · linarith only [h154, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h150, h154, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h153, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h158 | h158
        · linarith only [h158, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h160 | h160
          · rcases p0_3 (m.d 4 5) (by simp) with h161 | h161
            · linarith only [h148, h161, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h161, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h160, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h38, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h70, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h126, h134, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h125, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h151, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h179, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h174, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h208, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h236, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h264, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h263, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h284, h295, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h294, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h0ehi := hb0.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h70, h75, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · linarith only [h78, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h78, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 4) (by simp) with h84 | h84
      · rcases p0_3 (m.d 2 4) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · linarith only [h88, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h83, h88, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h85, h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h84, hlam, p0_0]
    · linarith only [h83, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h100 | h100
    · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
      · linarith only [h101, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h103 | h103
        · rcases p0_3 (m.d 3 4) (by simp) with h104 | h104
          · rcases p0_3 (m.d 4 5) (by simp) with h105 | h105
            · linarith only [h105, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h100, h105, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h103, hlam, p0_0]
    · linarith only [h100, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h119, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h123, hlam, p0_0]
    · linarith only [h114, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · rcases p0_3 (m.d 3 4) (by simp) with h137 | h137
          · rcases p0_3 (m.d 4 5) (by simp) with h138 | h138
            · linarith only [h138, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h133, h138, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h137, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h143, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h142, hlam, p0_0]
    · linarith only [h133, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 4) (by simp) with h149 | h149
      · rcases p0_3 (m.d 2 4) (by simp) with h150 | h150
        · linarith only [h150, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h148, h153, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h152, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h149, h160, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h159, hlam, p0_0]
    · linarith only [h148, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_L_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h0bigk := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
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
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h10, h14, h16, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h16, hc34, hlam, hphi, u4elo4]
                                · linarith only [h15, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h14, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h13, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h12, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                  · linarith only [h0, h10, h24, h27, h29, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h29, hc34, hlam, hphi, u4elo4]
                                · linarith only [h10, h28, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h10, h27, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h10, h24, h26, hc24, hlam, hphi, ht45, u5elo3]
                          · linarith only [h24, h25, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h24, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h9, hc04, hlam, hphi, u4elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1, h7, hc13, hlam, hphi, ht34, u4elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h42 | h42
            · rcases m.htr 0 2 5 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 3 4 (by decide) (by decide) with h44 | h44
                · rcases m.htr 0 3 5 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
                      · linarith only [h0, h4, h42, h47, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                                  · rcases h0bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h0, h49, h52, h54, hc01, hc45, hlam, hphi, ht0b, ht5b, p55_1]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h0, h4, h49, h52, h54, hc01, hc45, hlam, hphi, ht0b, ht5b, p55_1]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      rcases p55_3 (m.d 0 1) (by simp) with h59 | h59
                                      · rcases p55_3 (m.d 0 2) (by simp) with h60 | h60
                                        · linarith only [h0, h60, hlam]
                                        · linarith only [h42, h60, hlam]
                                      · linarith only [h2, h59, hlam]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      rcases p55_3 (m.d 0 1) (by simp) with h64 | h64
                                      · rcases p55_3 (m.d 0 2) (by simp) with h65 | h65
                                        · linarith only [h0, h65, hlam]
                                        · linarith only [h43, h65, hlam]
                                      · linarith only [h3, h64, hlam]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h0, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h4, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h2, h4, h49, h52, h54, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p55_1]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      rcases p55_3 (m.d 0 1) (by simp) with h73 | h73
                                      · rcases p55_3 (m.d 0 2) (by simp) with h74 | h74
                                        · rcases p55_3 (m.d 0 3) (by simp) with h75 | h75
                                          · rcases p55_3 (m.d 0 4) (by simp) with h76 | h76
                                            · linarith only [h42, h76, hlam]
                                            · linarith only [h46, h76, hlam]
                                          · linarith only [h45, h75, hlam]
                                        · linarith only [h43, h74, hlam]
                                      · linarith only [h3, h73, hlam]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h1, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h0, h49, h52, h54, hc03, hc45, hlam, hphi, ht0b, ht5b, p55_1]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      rcases p55_3 (m.d 0 1) (by simp) with h85 | h85
                                      · rcases p55_3 (m.d 0 2) (by simp) with h86 | h86
                                        · linarith only [h4, h86, hlam]
                                        · linarith only [h42, h86, hlam]
                                      · linarith only [h2, h85, hlam]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      rcases p55_3 (m.d 0 1) (by simp) with h90 | h90
                                      · rcases p55_3 (m.d 0 2) (by simp) with h91 | h91
                                        · linarith only [h4, h91, hlam]
                                        · linarith only [h43, h91, hlam]
                                      · linarith only [h3, h90, hlam]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h2, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h42, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h44, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h3, h50, h53, h54, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p55_1, u4elo0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h3, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h43, hlam, p55_1]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h45, hlam, p55_0]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [h46, hlam, p55_1]
                                    · obtain ⟨p55_0, p55_1, p55_2, p55_3⟩ := h55c
                                      linarith only [hlam, p55_0]
                                  · linarith only [h54, hc34, hlam, hphi, u4elo4]
                                · linarith only [h53, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h4, h52, hc03, hlam, hphi, ht34, u4elo3]
                            · linarith only [h47, h51, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h49, h50, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h49, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h46, hc04, hlam, hphi, u4elo4]
                  · linarith only [h4, h45, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h4, h42, h44, hc24, hlam, hphi, u4elo3]
              · linarith only [h42, h43, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h42, hc02, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h118 | h118
      · rcases m.htr 0 1 5 (by decide) (by decide) with h119 | h119
        · rcases m.htr 0 2 3 (by decide) (by decide) with h120 | h120
          · linarith only [h0, h1, h120, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h122 | h122
            · rcases m.htr 0 2 5 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
                · rcases m.htr 0 3 5 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                      · linarith only [h0, h1, h120, h127, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h131 | h131
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                                  · linarith only [h0, h1, h127, h129, h132, h134, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h134, hc34, hlam, hphi, u4elo4]
                                · linarith only [h0, h1, h127, h133, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h127, h129, h132, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h129, h131, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h129, h130, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h129, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h126, hc04, hlam, hphi, u4elo4]
                  · linarith only [h0, h1, h125, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h124, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h123, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h122, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h0, h119, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h118, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h149 | h149
    · rcases m.htr 0 1 4 (by decide) (by decide) with h150 | h150
      · rcases m.htr 0 1 5 (by decide) (by decide) with h151 | h151
        · rcases m.htr 0 2 3 (by decide) (by decide) with h152 | h152
          · rcases m.htr 0 2 4 (by decide) (by decide) with h153 | h153
            · rcases m.htr 0 2 5 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
                · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                                  · linarith only [h0, h149, h158, h162, h164, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h164, hc34, hlam, hphi, u4elo4]
                                · linarith only [h163, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h162, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h161, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h160, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h150, h153, h159, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h152, h158, hlam]
                    · linarith only [h157, hc04, hlam, hphi, u4elo4]
                  · linarith only [h155, h156, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h155, hc03, hlam, hphi, ht34, u4elo3]
              · linarith only [h154, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h153, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h0, h149, h152, hlam]
        · linarith only [h149, h151, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · linarith only [h149, h150, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h181 | h181
      · rcases m.htr 0 1 5 (by decide) (by decide) with h182 | h182
        · rcases m.htr 0 2 3 (by decide) (by decide) with h183 | h183
          · rcases m.htr 0 2 4 (by decide) (by decide) with h184 | h184
            · rcases m.htr 0 2 5 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 3 4 (by decide) (by decide) with h186 | h186
                · rcases m.htr 0 3 5 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h188 | h188
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h195 | h195
                                  · rcases h0bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h0, hlam, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h149, hlam, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h149, h181, h189, h190, h193, h195, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      rcases p196_3 (m.d 0 1) (by simp) with h201 | h201
                                      · rcases p196_3 (m.d 0 2) (by simp) with h202 | h202
                                        · rcases p196_3 (m.d 0 3) (by simp) with h203 | h203
                                          · rcases p196_3 (m.d 0 4) (by simp) with h204 | h204
                                            · linarith only [h181, h204, hlam]
                                            · linarith only [h188, h204, hlam]
                                          · linarith only [h187, h203, hlam]
                                        · linarith only [h185, h202, hlam]
                                      · linarith only [h182, h201, hlam]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h0, h181, h190, h193, h195, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h0, h149, h181, h190, h193, h195, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      rcases p196_3 (m.d 0 1) (by simp) with h213 | h213
                                      · linarith only [h0, h213, hlam]
                                      · linarith only [h181, h213, hlam]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      rcases p196_3 (m.d 0 1) (by simp) with h216 | h216
                                      · linarith only [h0, h216, hlam]
                                      · linarith only [h182, h216, hlam]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h181, h190, h193, h195, hc03, hc45, hlam, hphi, ht0b, ht5b, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h183, hlam, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      rcases p196_3 (m.d 0 1) (by simp) with h222 | h222
                                      · linarith only [h149, h222, hlam]
                                      · linarith only [h181, h222, hlam]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      rcases p196_3 (m.d 0 1) (by simp) with h225 | h225
                                      · linarith only [h149, h225, hlam]
                                      · linarith only [h182, h225, hlam]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h181, hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h184, hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h186, hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h182, h191, h194, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p196_1, u4elo0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h182, hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h185, hlam, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h187, hlam, p196_0]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [h188, hlam, p196_1]
                                    · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                                      linarith only [hlam, p196_0]
                                  · linarith only [h195, hc34, hlam, hphi, u4elo4]
                                · linarith only [h194, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h193, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h192, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h191, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h149, h182, h184, h189, h190, hc02, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h183, h189, hlam]
                    · linarith only [h188, hc04, hlam, hphi, u4elo4]
                  · linarith only [h187, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h186, hc03, hlam, hphi, ht34, u4elo3]
              · linarith only [h185, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h149, h181, h183, h184, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h250 | h250
            · rcases m.htr 0 2 5 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
                · rcases m.htr 0 3 5 (by decide) (by decide) with h253 | h253
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h254 | h254
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h258 | h258
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h261 | h261
                                  · linarith only [h0, h181, h183, h255, h256, h259, h261, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h261, hc34, hlam, hphi, u4elo4]
                                · linarith only [h0, h183, h260, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h183, h259, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                            · linarith only [h0, h181, h183, h255, h256, h258, hc24, hlam, hphi, ht45, u5elo3]
                          · linarith only [h0, h181, h183, h255, h256, h257, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h181, h183, h255, h256, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h270 | h270
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                                  · linarith only [h0, h181, h255, h269, h272, h274, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h274, hc34, hlam, hphi, u4elo4]
                                · linarith only [h0, h181, h255, h269, h272, h273, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h255, h272, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h181, h255, h269, h271, hc24, hlam, hphi, ht45, u5elo3]
                          · linarith only [h0, h181, h269, h270, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h181, h269, hc14, hlam, hphi, u4elo2]
                    · linarith only [h254, hc04, hlam, hphi, u4elo4]
                  · linarith only [h253, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h183, h252, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h0, h181, h251, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h181, h250, hc14, hlam, hphi, u4elo2]
        · linarith only [h181, h182, hc14, hlam, hphi, ht45, u5elo1]
      · linarith only [h181, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB0_H_R_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h4ehi := hb4.1
  have h0ehi := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h3, h6, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h9, hc45, hlam, hphi, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h1, h12, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h12, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
              · linarith only [h15, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
                · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h1, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h18, hc45, hlam, hphi, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h1, h21, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h21, hc45, hlam, hphi, u4ehi1]
          · linarith only [h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
            · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
              · linarith only [h27, h3, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                  · linarith only [h1, h30, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h30, hc45, hlam, hphi, u4ehi1]
                · linarith only [h25, h29, h3, hc12, hc24, hlam, hphi]
            · linarith only [h2, h26, h3, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
            · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h3, h36, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                · linarith only [h0, h25, h38, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                  · linarith only [h1, h40, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h40, hc45, hlam, hphi, u4ehi1]
            · linarith only [h2, h3, h35, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h44 | h44
        · linarith only [h2, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h46 | h46
          · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
            · linarith only [h2, h47, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
              · linarith only [h0, h44, h49, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                  · linarith only [h1, h52, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h52, hc45, hlam, hphi, u4ehi1]
                · linarith only [h2, h46, h51, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
            · linarith only [h2, h56, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
              · linarith only [h0, h2, h44, h58, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                · linarith only [h0, h46, h60, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                  · linarith only [h1, h62, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h62, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h65 | h65
      · rcases m.htr 0 2 4 (by decide) (by decide) with h66 | h66
        · linarith only [h0, h1, h66, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
          · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
            · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
              · linarith only [h0, h1, h66, h70, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
                · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                  · linarith only [h0, h1, h70, h72, h73, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1, h73, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h1, h68, h69, h72, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h65, h66, h69, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
            · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
              · linarith only [h66, h79, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                · linarith only [h0, h1, h65, h68, h79, h81, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                    · linarith only [h65, h84, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h1, h78, h79, h84, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h78, h83, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h65, h66, h78, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h89 | h89
        · linarith only [h65, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h91 | h91
          · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
            · linarith only [h65, h92, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
              · linarith only [h0, h1, h89, h91, h94, hc14, hlam, hphi, ht01, u0ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                  · linarith only [h0, h1, h94, h96, h97, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1, h97, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h65, h91, h96, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
            · linarith only [h101, h65, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
              · linarith only [h0, h1, h103, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                · linarith only [h0, h1, h103, h105, h91, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h108, h111, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h111, hc45, hlam, hphi, u4ehi3]
                        · linarith only [h103, h107, h110, hlam]
                      · linarith only [h0, h1, h103, h108, h109, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h108, h65, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h0, h1, h107, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h118 | h118
    · linarith only [h0, h118, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h120 | h120
      · rcases m.htr 0 2 4 (by decide) (by decide) with h121 | h121
        · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
          · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
            · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
              · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                    · linarith only [h120, h127, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                        · linarith only [h0, h121, h130, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h130, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                        · linarith only [h0, h121, h133, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h133, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h126, hc45, hlam, hphi, u4ehi1]
                · linarith only [h0, h125, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h124, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h120, h123, hlam]
          · linarith only [h121, h122, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h141 | h141
          · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
            · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
              · linarith only [h121, h143, hc12, hlam, hphi, ht01, u0ehi1]
              · linarith only [h0, h143, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h142, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
            · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
              · linarith only [h120, h121, h148, hc12, hlam, hphi, ht01, u0ehi2]
              · linarith only [h0, h148, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h120, h147, hc02, hlam, hphi, u0ehi0]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h152 | h152
        · linarith only [h120, h152, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h154 | h154
          · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
            · linarith only [h120, h155, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h155, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
            · linarith only [h120, h158, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h158, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem n7l_sAB0_H_R_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h0bigk := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                        · linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h11, h13, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h11, h15, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h15, hc45, hlam, hphi, u4ehi1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                        · linarith only [h10, h18, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h10, h20, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                            · linarith only [h2, h22, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h22, hc45, hlam, hphi, u4ehi1]
                    · linarith only [h9, hc45, hlam, hphi, u4ehi0]
                  · linarith only [h7, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
                  · linarith only [h27, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h31, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                          · linarith only [h0, h31, h33, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                            · linarith only [h2, h35, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h35, hc45, hlam, hphi, u4ehi1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                        · linarith only [h30, h38, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                          · linarith only [h30, h4, h40, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                            · linarith only [h2, h42, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h42, hc45, hlam, hphi, u4ehi1]
                    · linarith only [h29, hc45, hlam, hphi, u4ehi0]
              · linarith only [h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
              · linarith only [h47, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
                · linarith only [h4, h49, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
                  · linarith only [h4, h5, h51, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                        · linarith only [h0, h55, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h0, h47, h57, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                            · linarith only [h2, h59, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h49, h53, h59, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                      · linarith only [h4, h5, h54, hc12, hc24, hlam, hphi]
                    · linarith only [h53, hc45, hlam, hphi, u4ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h64 | h64
            · linarith only [h4, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h66 | h66
              · linarith only [h4, h66, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h4, h71, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                        · linarith only [h0, h64, h73, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                          · linarith only [h0, h66, h75, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h77 | h77
                            · linarith only [h2, h77, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h68, h70, h77, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h70, hc45, hlam, hphi, u4ehi0]
                  · linarith only [h68, h69, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h68, h82, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                      · linarith only [h0, h4, h85, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
                        · linarith only [h0, h4, h68, h87, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                          · linarith only [h0, h4, h68, h89, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                            · linarith only [h2, h91, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h91, hc45, hlam, hphi, u4ehi1]
                    · linarith only [h84, hc45, hlam, hphi, u4ehi0]
        · linarith only [h2, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
        · linarith only [h2, h96, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h98 | h98
          · rcases m.htr 0 2 4 (by decide) (by decide) with h99 | h99
            · linarith only [h0, h2, h99, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h101 | h101
              · linarith only [h0, h101, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h103 | h103
                · linarith only [h1, h103, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h105, h2, h98, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                        · linarith only [h0, h109, h2, h99, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h0, h101, h109, h111, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                              · linarith only [h0, h103, h107, h108, h109, h113, h114, h96, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h108, h109, h113, h114, h96, hc23, hc34, hlam, hphi]
                            · linarith only [h107, h113, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h108, h98, h99, hc12, hc24, hlam, hphi]
                    · linarith only [h107, hc45, hlam, hphi, u4ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
            · linarith only [h1, h120, h2, h98, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
              · linarith only [h1, h122, h2, h98, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
                · linarith only [h1, h124, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h126 | h126
                  · linarith only [h124, h126, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                      · linarith only [h0, h129, h2, h98, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h131 | h131
                        · linarith only [h0, h120, h128, h131, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                          · linarith only [h1, h122, h129, h131, h133, h2, hc02, hc24, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                              · linarith only [h124, h128, h136, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                                · linarith only [h126, h136, h138, hc03, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                                    · rcases h0bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h0, h131, h135, h136, h96, hc12, hc34, hlam, hphi, ht23, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h0, h131, h135, h136, h96, h98, hc12, hc34, hlam, hphi, ht23, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h2, hlam, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h96, hlam, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h0, hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h98, hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h120, hlam, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h122, hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h1, hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h0, h1, h131, h135, h136, h96, hc12, hc34, hlam, hphi, ht23, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h124, hlam, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h126, hlam, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h0, h131, h136, h2, hc12, hc34, hlam, hphi, ht23, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        rcases p142_3 (m.d 0 1) (by simp) with h159 | h159
                                        · linarith only [h159, h2, hlam]
                                        · linarith only [h0, h159, hlam]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        rcases p142_3 (m.d 0 1) (by simp) with h162 | h162
                                        · linarith only [h162, h2, hlam]
                                        · linarith only [h1, h162, hlam]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [hlam, p142_0]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h128, h131, h136, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p142_1, u4ehi4]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h1, h129, h131, h135, h136, h96, hc12, hc34, hlam, hphi, ht23, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        rcases p142_3 (m.d 0 1) (by simp) with h168 | h168
                                        · linarith only [h168, h96, hlam]
                                        · linarith only [h0, h168, hlam]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        rcases p142_3 (m.d 0 1) (by simp) with h171 | h171
                                        · linarith only [h171, h96, hlam]
                                        · linarith only [h1, h171, hlam]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [h128, hlam, p142_1]
                                      · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                                        linarith only [hlam, p142_0]
                                    · linarith only [h131, h136, h141, h2, hc45, hlam, hphi, u4ehi0]
                                  · linarith only [h128, h131, h140, h2, hlam]
                            · linarith only [h128, h135, h2, hlam]
                    · linarith only [h128, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h180 | h180
      · linarith only [h1, h180, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h182 | h182
        · linarith only [h1, h182, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h184 | h184
          · linarith only [h0, h1, h184, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
            · linarith only [h0, h1, h186, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h188 | h188
              · linarith only [h0, h1, h188, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h190 | h190
                · rcases m.htr 0 3 5 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h192 | h192
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
                      · linarith only [h0, h1, h184, h193, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
                        · linarith only [h0, h186, h192, h195, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                          · linarith only [h0, h1, h188, h193, h197, hc02, hc23, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                                    · linarith only [h190, h203, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h192, h203, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h180, h192, h195, h202, hlam]
                                · linarith only [h0, h182, h195, h199, h200, h201, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h190, h192, h193, h200, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h180, h192, h199, hlam]
                    · linarith only [h192, hc45, hlam, hphi, u4ehi0]
                  · linarith only [h190, h191, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h212 | h212
                  · linarith only [h190, h212, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
                      · linarith only [h0, h1, h190, h215, hc23, hc34, hlam, hphi]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                        · linarith only [h0, h1, h190, h217, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                          · linarith only [h0, h1, h188, h190, h219, hc02, hc34, hlam, hphi, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                              · linarith only [h0, h1, h190, h222, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h1, h215, h222, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h180, h214, h221, hlam]
                    · linarith only [h214, hc45, hlam, hphi, u4ehi0]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h227 | h227
    · rcases m.htr 0 1 4 (by decide) (by decide) with h228 | h228
      · linarith only [h0, h228, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h230 | h230
        · linarith only [h0, h230, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h232 | h232
          · rcases m.htr 0 2 4 (by decide) (by decide) with h233 | h233
            · rcases m.htr 0 2 5 (by decide) (by decide) with h234 | h234
              · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
                · linarith only [h0, h227, h235, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h237 | h237
                  · linarith only [h235, h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                              · linarith only [h227, h230, h240, h241, h243, h244, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                                · linarith only [h227, h230, h237, h240, h241, h243, h246, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                                  · linarith only [h233, h248, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h235, h239, h248, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h235, h239, h243, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                          · linarith only [h0, h233, h239, h242, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h233, h241, hlam]
                      · linarith only [h0, h233, h239, h240, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h239, hc45, hlam, hphi, u4ehi0]
              · linarith only [h233, h234, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h257 | h257
              · linarith only [h233, h257, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
                · linarith only [h0, h227, h259, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
                  · linarith only [h0, h227, h233, h261, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h265 | h265
                        · linarith only [h233, h263, h265, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                          · linarith only [h0, h257, h265, h267, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                              · linarith only [h227, h259, h263, h264, h270, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h227, h264, h265, h270, hc23, hc34, hlam, hphi]
                            · linarith only [h228, h263, h269, hlam]
                      · linarith only [h0, h232, h264, hlam]
                    · linarith only [h263, hc45, hlam, hphi, u4ehi0]
          · linarith only [h0, h227, h232, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h277 | h277
      · linarith only [h0, h277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h279 | h279
        · linarith only [h0, h279, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h281 | h281
          · rcases m.htr 0 2 4 (by decide) (by decide) with h282 | h282
            · rcases m.htr 0 2 5 (by decide) (by decide) with h283 | h283
              · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
                · rcases m.htr 0 3 5 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                              · linarith only [h281, h291, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                                · linarith only [h227, h284, h287, h291, h293, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                                  · linarith only [h227, h284, h287, h291, h295, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h286, h295, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h227, h284, h286, h287, h290, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h227, h284, h287, h289, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h227, h284, h287, h288, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h281, h284, h286, h287, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h286, hc45, hlam, hphi, u4ehi0]
                  · linarith only [h284, h285, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h304 | h304
                  · linarith only [h284, h304, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h308 | h308
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                              · linarith only [h0, h281, h311, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                                · linarith only [h0, h281, h304, h306, h313, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h315 | h315
                                  · linarith only [h0, h282, h315, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h284, h306, h315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h277, h306, h310, hlam]
                          · linarith only [h0, h279, h282, h283, h309, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h282, h306, h308, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h281, h282, h284, h306, h307, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h306, hc45, hlam, hphi, u4ehi0]
              · linarith only [h282, h283, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h324 | h324
              · linarith only [h282, h324, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h326 | h326
                · linarith only [h281, h282, h326, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h328 | h328
                  · linarith only [h281, h282, h328, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h330 | h330
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
                        · linarith only [h282, h330, h332, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                          · linarith only [h324, h332, h334, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                              · linarith only [h281, h326, h330, h337, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                                · linarith only [h0, h281, h328, h332, h337, h339, hc03, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h341 | h341
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                                    · rcases h0bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [hlam, p343_0]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h0, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h227, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h277, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h279, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h0, h334, h337, h341, hc01, hc34, hlam, hphi, ht12, ht23, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [hlam, p343_0]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h0, h227, h334, h337, h341, hc01, hc34, hlam, hphi, ht12, ht23, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h282, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h324, hlam, p343_0]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h0, h281, h334, h337, h341, hc01, hc34, hlam, hphi, ht12, ht23, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h281, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [hlam, p343_0]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h326, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h328, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        rcases p343_3 (m.d 0 1) (by simp) with h359 | h359
                                        · linarith only [h277, h359, hlam]
                                        · rcases p343_3 (m.d 0 2) (by simp) with h361 | h361
                                          · linarith only [h282, h361, hlam]
                                          · linarith only [h0, h361, hlam]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h277, h281, h332, h337, hc23, hc34, hlam, hphi, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        rcases p343_3 (m.d 0 1) (by simp) with h365 | h365
                                        · linarith only [h277, h365, hlam]
                                        · rcases p343_3 (m.d 0 2) (by simp) with h367 | h367
                                          · linarith only [h282, h367, hlam]
                                          · linarith only [h281, h367, hlam]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [hlam, p343_0]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h277, h330, h332, h337, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p343_1, u4ehi4]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        rcases p343_3 (m.d 0 1) (by simp) with h372 | h372
                                        · linarith only [h279, h372, hlam]
                                        · rcases p343_3 (m.d 0 2) (by simp) with h374 | h374
                                          · linarith only [h324, h374, hlam]
                                          · linarith only [h0, h374, hlam]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h279, h281, h332, h336, h337, hc23, hc34, hlam, hphi, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        rcases p343_3 (m.d 0 1) (by simp) with h378 | h378
                                        · linarith only [h279, h378, hlam]
                                        · rcases p343_3 (m.d 0 2) (by simp) with h380 | h380
                                          · linarith only [h324, h380, hlam]
                                          · linarith only [h281, h380, hlam]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [h330, hlam, p343_1]
                                      · obtain ⟨p343_0, p343_1, p343_2, p343_3⟩ := h343c
                                        linarith only [hlam, p343_0]
                                    · linarith only [h277, h332, h337, h342, hc45, hlam, hphi, u4ehi0]
                                  · linarith only [h277, h330, h332, h341, hlam]
                            · linarith only [h277, h330, h336, hlam]
                      · linarith only [h0, h281, h331, hlam]
                    · linarith only [h330, hc45, hlam, hphi, u4ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h390 | h390
            · linarith only [h281, h390, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h392 | h392
              · linarith only [h281, h392, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h394 | h394
                · rcases m.htr 0 3 5 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h396 | h396
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h397 | h397
                      · linarith only [h281, h394, h396, h397, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                        · linarith only [h390, h397, h399, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h401 | h401
                          · linarith only [h392, h397, h401, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h405 | h405
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                                    · linarith only [h227, h394, h397, h407, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                    · linarith only [h407, hc45, hlam, hphi, u4ehi3]
                                  · linarith only [h227, h394, h396, h397, h406, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                                · linarith only [h227, h394, h396, h397, h405, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · linarith only [h227, h394, h396, h397, h404, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h277, h396, h403, hlam]
                    · linarith only [h396, hc45, hlam, hphi, u4ehi0]
                  · linarith only [h394, h395, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h416 | h416
                  · linarith only [h394, h416, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
                        · linarith only [h390, h418, h420, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h281, h419, h420, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                        · linarith only [h419, h423, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                          · linarith only [h419, h425, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h428 | h428
                              · linarith only [h394, h418, h428, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h419, h428, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h418, h427, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h418, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB0_M_IR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h11, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h14, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 4 5) (by simp) with h18 | h18
            · linarith only [h18, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h18, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h21, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h26 | h26
    · linarith only [h26, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
    · rcases p0_3 (m.d 1 4) (by simp) with h28 | h28
      · rcases p0_3 (m.d 2 4) (by simp) with h29 | h29
        · linarith only [h29, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h31 | h31
          · rcases p0_3 (m.d 4 5) (by simp) with h32 | h32
            · linarith only [h32, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h32, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h26, h35, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h35, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h28, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h39 | h39
    · linarith only [h39, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h41 | h41
      · rcases p0_3 (m.d 2 4) (by simp) with h42 | h42
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h45, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h45, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h48 | h48
          · linarith only [h48, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h50 | h50
            · linarith only [h39, h50, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h50, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h41, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · rcases p0_3 (m.d 2 4) (by simp) with h58 | h58
        · rcases p0_3 (m.d 3 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h60, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h63, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h58, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h67 | h67
        · rcases p0_3 (m.d 3 4) (by simp) with h68 | h68
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · linarith only [h69, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h69, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h72 | h72
            · linarith only [h72, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h72, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h67, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
    · linarith only [h76, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
    · rcases p0_3 (m.d 1 4) (by simp) with h78 | h78
      · linarith only [h78, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h80 | h80
        · rcases p0_3 (m.d 3 4) (by simp) with h81 | h81
          · rcases p0_3 (m.d 4 5) (by simp) with h82 | h82
            · linarith only [h82, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h82, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h76, h85, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h80, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · linarith only [h90, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · linarith only [h94, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h92, h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h93, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h100 | h100
        · rcases p0_3 (m.d 3 4) (by simp) with h101 | h101
          · linarith only [h101, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h103 | h103
            · linarith only [h103, h90, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h103, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h108 | h108
    · linarith only [h108, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h110 | h110
      · rcases p0_3 (m.d 2 4) (by simp) with h111 | h111
        · rcases p0_3 (m.d 3 4) (by simp) with h112 | h112
          · rcases p0_3 (m.d 4 5) (by simp) with h113 | h113
            · linarith only [h113, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h110, h113, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h112, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h117, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h122 | h122
        · rcases p0_3 (m.d 3 4) (by simp) with h123 | h123
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h122, h124, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h123, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h128, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · linarith only [h133, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
    · rcases p0_3 (m.d 1 4) (by simp) with h135 | h135
      · linarith only [h135, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h137 | h137
        · rcases p0_3 (m.d 3 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 4 5) (by simp) with h139 | h139
            · linarith only [h139, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h137, h139, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h138, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h133, h144, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h143, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · linarith only [h148, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · linarith only [h151, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h153 | h153
          · rcases p0_3 (m.d 4 5) (by simp) with h154 | h154
            · linarith only [h154, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h150, h154, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h153, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h158 | h158
        · linarith only [h158, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h160 | h160
          · rcases p0_3 (m.d 4 5) (by simp) with h161 | h161
            · linarith only [h148, h161, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h161, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h160, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_IR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h70, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h88, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h100, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h125, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h160, h179, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h174, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h208, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h236, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h263, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h294, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_IR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have h0ehi := hb0.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h70, h75, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · linarith only [h78, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h78, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 4) (by simp) with h84 | h84
      · rcases p0_3 (m.d 2 4) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · linarith only [h88, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h83, h88, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h85, h93, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h84, hlam, p0_0]
    · linarith only [h83, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h100 | h100
    · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
      · linarith only [h101, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h103 | h103
        · rcases p0_3 (m.d 3 4) (by simp) with h104 | h104
          · rcases p0_3 (m.d 4 5) (by simp) with h105 | h105
            · linarith only [h105, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h100, h105, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h103, hlam, p0_0]
    · linarith only [h100, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h114, h119, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h123, hlam, p0_0]
    · linarith only [h114, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · rcases p0_3 (m.d 3 4) (by simp) with h137 | h137
          · rcases p0_3 (m.d 4 5) (by simp) with h138 | h138
            · linarith only [h138, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h133, h138, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h137, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h143, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h142, hlam, p0_0]
    · linarith only [h133, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h148 | h148
    · rcases p0_3 (m.d 1 4) (by simp) with h149 | h149
      · rcases p0_3 (m.d 2 4) (by simp) with h150 | h150
        · linarith only [h150, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h148, h153, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h152, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h149, h160, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
    · linarith only [h148, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_IR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
              · linarith only [h13, hlam, p0_0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h9, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
                  · linarith only [h10, h17, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h19, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h11, h19, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · linarith only [h22, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
              · linarith only [h24, hlam, p0_0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h26 | h26
                · linarith only [h26, h9, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h29, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h22, h29, hlam]
                  · linarith only [h10, h28, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h33 | h33
          · rcases p0_3 (m.d 4 5) (by simp) with h34 | h34
            · linarith only [h34, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
              · linarith only [h36, hlam, p0_0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h38 | h38
                · rcases m.htr 0 3 4 (by decide) (by decide) with h39 | h39
                  · linarith only [h33, h38, h39, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h33, h41, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                    · linarith only [h34, h41, hlam]
                · linarith only [h38, h9, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h45, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h47 | h47
              · linarith only [h47, hlam, p0_0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h49 | h49
                · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h51, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h45, h51, hlam]
                  · linarith only [h33, h50, hlam]
                · linarith only [h49, h9, hlam]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
    · linarith only [h58, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
    · rcases p0_3 (m.d 1 4) (by simp) with h60 | h60
      · rcases p0_3 (m.d 2 4) (by simp) with h61 | h61
        · linarith only [h61, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h63 | h63
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · linarith only [h64, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
              · linarith only [h66, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h68 | h68
                · linarith only [h58, h68, hlam]
                · linarith only [h63, h68, hc02, hc34, hlam, hphi, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h71 | h71
            · linarith only [h71, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
              · linarith only [h73, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h75 | h75
                · linarith only [h58, h75, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h75, h78, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                    · linarith only [h71, h73, h78, hc01, hc14, hlam, hphi, p0_1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h81 | h81
                    · linarith only [h75, h81, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                    · linarith only [h71, h81, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h60, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h85 | h85
    · linarith only [h85, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h87 | h87
      · rcases p0_3 (m.d 2 4) (by simp) with h88 | h88
        · rcases p0_3 (m.d 3 4) (by simp) with h89 | h89
          · linarith only [h89, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h91 | h91
            · linarith only [h91, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h93 | h93
              · linarith only [h93, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h95 | h95
                · linarith only [h88, h95, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi3]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h85, h97, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h97, h99, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h88, h91, h93, h99, hc01, hc24, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h102 | h102
          · linarith only [h102, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
              · linarith only [h106, h88, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h108 | h108
                · rcases m.htr 0 3 4 (by decide) (by decide) with h109 | h109
                  · linarith only [h109, h85, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                    · linarith only [h109, h111, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h104, h106, h111, hc01, hc14, hlam, hphi, p0_1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
                  · linarith only [h114, h85, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
                    · linarith only [h114, h116, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                    · linarith only [h104, h116, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h87, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h120 | h120
    · linarith only [h120, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi4]
    · rcases p0_3 (m.d 1 4) (by simp) with h122 | h122
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · rcases p0_3 (m.d 4 5) (by simp) with h125 | h125
            · linarith only [h125, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h127 | h127
              · linarith only [h127, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi4]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h129 | h129
                · linarith only [h123, h129, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi4]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
                  · linarith only [h124, h131, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
                    · linarith only [h120, h133, hlam]
                    · linarith only [h133, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h136 | h136
            · linarith only [h136, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
              · linarith only [h124, h138, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h140 | h140
                · linarith only [h123, h124, h140, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi3]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
                    · linarith only [h120, h143, hlam]
                    · linarith only [h142, h143, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
                    · linarith only [h120, h146, hlam]
                    · linarith only [h123, h138, h146, hc01, hc24, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h149 | h149
          · rcases p0_3 (m.d 4 5) (by simp) with h150 | h150
            · linarith only [h150, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h152 | h152
              · linarith only [h123, h152, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h154 | h154
                · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
                  · linarith only [h120, h149, h154, h155, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h157 | h157
                    · linarith only [h120, h157, hlam]
                    · linarith only [h154, h157, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                · linarith only [h123, h149, h154, hc02, hc34, hlam, hphi, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h161 | h161
            · linarith only [h161, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h163 | h163
              · linarith only [h123, h163, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h165 | h165
                · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
                    · linarith only [h120, h167, hlam]
                    · linarith only [h165, h167, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h170 | h170
                    · linarith only [h120, h170, hlam]
                    · linarith only [h165, h170, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h173 | h173
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h174 | h174
                    · linarith only [h120, h174, hlam]
                    · linarith only [h163, h174, hc01, hc14, hlam, hphi, p0_1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                    · linarith only [h120, h177, hlam]
                    · linarith only [h177, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
      · linarith only [h122, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h181 | h181
    · linarith only [h181, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h183 | h183
      · rcases p0_3 (m.d 2 4) (by simp) with h184 | h184
        · rcases p0_3 (m.d 3 4) (by simp) with h185 | h185
          · rcases p0_3 (m.d 4 5) (by simp) with h186 | h186
            · linarith only [h186, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h188 | h188
              · linarith only [h183, h188, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h190 | h190
                · linarith only [h190, hlam, p0_0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
                  · linarith only [h185, h192, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
                    · linarith only [h183, h194, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h186, h194, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h197 | h197
            · linarith only [h197, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h199 | h199
              · linarith only [h183, h199, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h201 | h201
                · linarith only [h201, hlam, p0_0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h204 | h204
                    · linarith only [h183, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h197, h204, hlam]
                  · linarith only [h185, h203, hlam]
        · linarith only [h184, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h209 | h209
        · rcases p0_3 (m.d 3 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h211, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h213 | h213
              · rcases m.htr 0 2 4 (by decide) (by decide) with h214 | h214
                · linarith only [h214, hlam, p0_0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h216 | h216
                  · linarith only [h210, h213, h216, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
                    · linarith only [h218, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                    · linarith only [h211, h218, hlam]
              · linarith only [h183, h213, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h222 | h222
            · linarith only [h222, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h224 | h224
              · rcases m.htr 0 2 4 (by decide) (by decide) with h225 | h225
                · linarith only [h225, hlam, p0_0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h227 | h227
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
                    · linarith only [h228, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                    · linarith only [h222, h228, hlam]
                  · linarith only [h210, h227, hlam]
              · linarith only [h183, h224, hlam]
        · linarith only [h209, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h234 | h234
    · linarith only [h234, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
    · rcases p0_3 (m.d 1 4) (by simp) with h236 | h236
      · linarith only [h236, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h238 | h238
        · rcases p0_3 (m.d 3 4) (by simp) with h239 | h239
          · rcases p0_3 (m.d 4 5) (by simp) with h240 | h240
            · linarith only [h240, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h242 | h242
              · linarith only [h234, h242, hlam]
              · linarith only [h242, hc01, hc24, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h245 | h245
            · linarith only [h234, h245, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h247 | h247
              · linarith only [h234, h247, hlam]
              · linarith only [h247, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h238, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h252 | h252
    · linarith only [h252, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h254 | h254
      · rcases p0_3 (m.d 2 4) (by simp) with h255 | h255
        · rcases p0_3 (m.d 3 4) (by simp) with h256 | h256
          · linarith only [h256, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h258 | h258
            · linarith only [h258, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h260 | h260
              · linarith only [h254, h260, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h262 | h262
                · linarith only [h262, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi3]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h264 | h264
                  · linarith only [h252, h264, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h266 | h266
                    · linarith only [h254, h264, h266, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h258, h260, h266, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · rcases p0_3 (m.d 3 4) (by simp) with h271 | h271
          · linarith only [h271, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h254, h273, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h275 | h275
              · rcases m.htr 0 2 4 (by decide) (by decide) with h276 | h276
                · linarith only [h252, h275, h276, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h278 | h278
                  · linarith only [h252, h278, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
                    · linarith only [h278, h280, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                    · linarith only [h273, h275, h280, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h254, h275, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h270, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h285 | h285
    · linarith only [h285, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi4]
    · rcases p0_3 (m.d 1 4) (by simp) with h287 | h287
      · rcases p0_3 (m.d 2 4) (by simp) with h288 | h288
        · rcases p0_3 (m.d 3 4) (by simp) with h289 | h289
          · rcases p0_3 (m.d 4 5) (by simp) with h290 | h290
            · linarith only [h290, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h292 | h292
              · linarith only [h287, h292, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi4]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h294 | h294
                · linarith only [h294, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi4]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h296 | h296
                  · linarith only [h289, h296, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h298 | h298
                    · linarith only [h285, h298, hlam]
                    · linarith only [h287, h298, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h301 | h301
            · linarith only [h301, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h303 | h303
              · linarith only [h287, h289, h303, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h305 | h305
                · linarith only [h289, h305, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi3]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h307 | h307
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
                    · linarith only [h285, h308, hlam]
                    · linarith only [h287, h307, h308, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h311 | h311
                    · linarith only [h285, h311, hlam]
                    · linarith only [h303, h311, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h288, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h315 | h315
        · rcases p0_3 (m.d 3 4) (by simp) with h316 | h316
          · rcases p0_3 (m.d 4 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h319 | h319
              · rcases m.htr 0 2 4 (by decide) (by decide) with h320 | h320
                · linarith only [h285, h320, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h322 | h322
                  · linarith only [h285, h316, h319, h322, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                    · linarith only [h285, h324, hlam]
                    · linarith only [h319, h324, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h287, h316, h319, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h328 | h328
            · linarith only [h328, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h330 | h330
              · rcases m.htr 0 2 4 (by decide) (by decide) with h331 | h331
                · linarith only [h316, h331, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi3]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                    · linarith only [h285, h334, hlam]
                    · linarith only [h330, h334, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h337 | h337
                    · linarith only [h285, h337, hlam]
                    · linarith only [h330, h337, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h287, h330, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h315, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h342 | h342
    · linarith only [h342, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h344 | h344
      · rcases p0_3 (m.d 2 4) (by simp) with h345 | h345
        · rcases p0_3 (m.d 3 4) (by simp) with h346 | h346
          · rcases p0_3 (m.d 4 5) (by simp) with h347 | h347
            · linarith only [h347, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h349 | h349
              · linarith only [h344, h349, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h351 | h351
                · linarith only [h345, h351, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h353 | h353
                  · linarith only [h353, hlam, p0_0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h355 | h355
                    · linarith only [h344, h355, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h347, h355, hlam]
          · linarith only [h346, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h359 | h359
          · rcases p0_3 (m.d 4 5) (by simp) with h360 | h360
            · linarith only [h360, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h362 | h362
              · linarith only [h344, h362, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h364 | h364
                · rcases m.htr 0 3 4 (by decide) (by decide) with h365 | h365
                  · linarith only [h365, hlam, p0_0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h367 | h367
                    · linarith only [h344, h367, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                    · linarith only [h360, h367, hlam]
                · linarith only [h345, h364, hlam]
          · linarith only [h359, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h372 | h372
        · rcases p0_3 (m.d 3 4) (by simp) with h373 | h373
          · rcases p0_3 (m.d 4 5) (by simp) with h374 | h374
            · linarith only [h374, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h376 | h376
              · rcases m.htr 0 2 4 (by decide) (by decide) with h377 | h377
                · linarith only [h372, h376, h377, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h379 | h379
                  · linarith only [h379, hlam, p0_0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
                    · linarith only [h372, h381, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                    · linarith only [h374, h381, hlam]
              · linarith only [h344, h376, hlam]
          · linarith only [h373, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h386 | h386
          · rcases p0_3 (m.d 4 5) (by simp) with h387 | h387
            · linarith only [h387, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h389 | h389
              · rcases m.htr 0 2 4 (by decide) (by decide) with h390 | h390
                · rcases m.htr 0 3 4 (by decide) (by decide) with h391 | h391
                  · linarith only [h391, hlam, p0_0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h393 | h393
                    · linarith only [h393, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                    · linarith only [h387, h393, hlam]
                · linarith only [h372, h390, hlam]
              · linarith only [h344, h389, hlam]
          · linarith only [h386, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h399 | h399
    · linarith only [h399, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
    · rcases p0_3 (m.d 1 4) (by simp) with h401 | h401
      · linarith only [h401, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h403 | h403
        · rcases p0_3 (m.d 3 4) (by simp) with h404 | h404
          · rcases p0_3 (m.d 4 5) (by simp) with h405 | h405
            · linarith only [h405, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h407 | h407
              · linarith only [h399, h407, hlam]
              · linarith only [h403, h407, hc01, hc24, hlam, hphi, ht12, p0_1]
          · linarith only [h404, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h411 | h411
          · rcases p0_3 (m.d 4 5) (by simp) with h412 | h412
            · linarith only [h399, h412, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h414 | h414
              · linarith only [h399, h414, hlam]
              · linarith only [h414, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h411, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h418 | h418
    · linarith only [h418, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
    · rcases p0_3 (m.d 1 4) (by simp) with h420 | h420
      · rcases p0_3 (m.d 2 4) (by simp) with h421 | h421
        · linarith only [h421, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h423 | h423
          · rcases p0_3 (m.d 4 5) (by simp) with h424 | h424
            · linarith only [h424, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h426 | h426
              · linarith only [h420, h426, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h428 | h428
                · linarith only [h418, h428, hlam]
                · linarith only [h428, hc02, hc34, hlam, hphi, ht23, p0_1]
          · linarith only [h423, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h432 | h432
        · linarith only [h432, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 4 5) (by simp) with h435 | h435
            · linarith only [h420, h435, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h437 | h437
              · rcases m.htr 0 2 4 (by decide) (by decide) with h438 | h438
                · linarith only [h418, h438, hlam]
                · linarith only [h438, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h420, h437, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h434, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h444 | h444
    · linarith only [h444, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi4]
    · rcases p0_3 (m.d 1 4) (by simp) with h446 | h446
      · rcases p0_3 (m.d 2 4) (by simp) with h447 | h447
        · rcases p0_3 (m.d 3 4) (by simp) with h448 | h448
          · rcases p0_3 (m.d 4 5) (by simp) with h449 | h449
            · linarith only [h449, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h451 | h451
              · linarith only [h446, h451, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi4]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h453 | h453
                · linarith only [h447, h453, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi4]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h455 | h455
                  · linarith only [h455, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h457 | h457
                    · linarith only [h444, h457, hlam]
                    · linarith only [h446, h457, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
          · linarith only [h448, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h461 | h461
          · rcases p0_3 (m.d 4 5) (by simp) with h462 | h462
            · linarith only [h462, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h464 | h464
              · linarith only [h446, h447, h464, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 3 4 (by decide) (by decide) with h467 | h467
                  · linarith only [h444, h466, h467, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h469 | h469
                    · linarith only [h444, h469, hlam]
                    · linarith only [h446, h466, h469, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                · linarith only [h447, h466, hc02, hc34, hlam, hphi, ht23, p0_1]
          · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h474 | h474
        · rcases p0_3 (m.d 3 4) (by simp) with h475 | h475
          · rcases p0_3 (m.d 4 5) (by simp) with h476 | h476
            · linarith only [h476, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h478 | h478
              · rcases m.htr 0 2 4 (by decide) (by decide) with h479 | h479
                · linarith only [h444, h474, h479, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h481 | h481
                  · linarith only [h444, h478, h481, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h483 | h483
                    · linarith only [h444, h483, hlam]
                    · linarith only [h474, h478, h483, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
              · linarith only [h446, h478, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h475, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h488 | h488
          · rcases p0_3 (m.d 4 5) (by simp) with h489 | h489
            · linarith only [h489, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h491 | h491
              · rcases m.htr 0 2 4 (by decide) (by decide) with h492 | h492
                · rcases m.htr 0 3 4 (by decide) (by decide) with h493 | h493
                  · linarith only [h444, h493, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
                    · linarith only [h444, h495, hlam]
                    · linarith only [h492, h495, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                · linarith only [h474, h492, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h446, h491, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h488, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_IR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
          · linarith only [h4, hlam, hphi, ht45, u4ehi1, u5elo4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
          · linarith only [h7, hlam, hphi, ht45, u4ehi1, u5elo4]
      · linarith only [h2, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h1, h11, h12, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
          · linarith only [h0, h14, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
          · linarith only [h11, h14, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
      · linarith only [h11, hlam, hphi, ht45, u4ehi0, u5elo4]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h18 | h18
    · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
      · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
        · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h18, h23, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
              · linarith only [h23, hlam, hphi, ht45, u4ehi2, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
              · linarith only [h18, h26, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
              · linarith only [h26, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h18, h19, h21, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
        · linarith only [h0, h18, h19, h20, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
      · linarith only [h19, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
      · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
        · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
            · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
              · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                · rcases h4bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h0, hlam, p38_1]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h18, hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h37, hlam, hphi, ht0b, ht45, ht5b, p38_1, u0elo3, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h18, h33, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h32, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h18, h32, h33, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h33, h37, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    rcases p38_3 (m.d 0 4) (by simp) with h48 | h48
                    · linarith only [h0, h48, hlam]
                    · linarith only [h32, h48, hlam]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h32, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h33, hlam, p38_1]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h33, h37, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h33, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h32, h35, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h35, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u4ehi1]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h35, hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h35, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u4ehi4]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h32, hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h34, hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h36, hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [h37, hlam, p38_0]
                  · obtain ⟨p38_0, p38_1, p38_2, p38_3⟩ := h38c
                    linarith only [hlam, p38_0]
                · linarith only [h32, h37, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · linarith only [h18, h32, h36, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
              · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                · rcases h4bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h0, hlam, p70_1]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h18, hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h18, h33, h35, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h18, h33, hc12, hlam, hphi, ht01, ht0b, ht5b, p70_1, u5ehi9]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h32, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p70_1, u4ehi4]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h18, h32, h33, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p70_1, u4ehi4]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h18, h32, h33, h35, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p70_1, u4ehi4]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    rcases p70_3 (m.d 0 4) (by simp) with h80 | h80
                    · linarith only [h0, h80, hlam]
                    · linarith only [h32, h80, hlam]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h32, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p70_1, u4ehi4]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h33, hlam, p70_1]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h35, hlam, p70_1]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h33, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p70_1, u4ehi4]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h32, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p70_1, u4ehi4]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p70_1]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h18, hc02, hc34, hlam, hphi, ht23, p70_1]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    rcases p70_3 (m.d 0 4) (by simp) with h92 | h92
                    · linarith only [h18, h35, h92, hlam]
                    · linarith only [h32, h92, hlam]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h32, hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h34, hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h68, hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [h69, hlam, p70_0]
                  · obtain ⟨p70_0, p70_1, p70_2, p70_3⟩ := h70c
                    linarith only [hlam, p70_0]
                · linarith only [h18, h32, h35, h69, hlam]
              · linarith only [h18, h32, h68, hlam]
          · linarith only [h18, h32, h33, h34, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
          · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
            · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
              · rcases m.htr 3 4 5 (by decide) (by decide) with h106 | h106
                · rcases h4bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h0, hlam, p107_1]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h18, hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [hlam, hphi, ht0b, ht45, ht5b, p107_1, u0elo3, u4ehi3]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [hlam, hphi, ht0b, ht45, ht5b, p107_1, u0elo3, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h32, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p107_1, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h33, hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h104, h106, h33, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p107_1, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    rcases p107_3 (m.d 0 4) (by simp) with h117 | h117
                    · linarith only [h0, h117, hlam]
                    · linarith only [h117, h32, hlam]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h104, h32, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p107_1, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h0, h104, hc01, hc23, hlam, hphi, ht12, p107_1]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h104, h106, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p107_1, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    rcases p107_3 (m.d 0 4) (by simp) with h124 | h124
                    · linarith only [h124, h18, hlam]
                    · linarith only [h124, h32, hlam]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h32, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p107_1, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h0, h104, h32, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p107_1, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h104, hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h104, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p107_1, u4ehi4]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h32, hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h103, hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h105, hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [h106, hlam, p107_0]
                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                    linarith only [hlam, p107_0]
                · linarith only [h106, h32, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
              · linarith only [h105, h32, h33, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
              · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                · rcases h4bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h0, hlam, p141_1]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h18, hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h0, h104, h33, hlam, p141_1]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [hlam, hphi, ht0b, ht5b, p141_1, u0elo3, u5ehi9]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h104, h32, h33, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u4ehi4]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h33, hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h104, h33, hlam, p141_1]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    rcases p141_3 (m.d 0 4) (by simp) with h151 | h151
                    · linarith only [h0, h151, hlam]
                    · linarith only [h151, h32, hlam]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h104, h32, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u4ehi4]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h0, h104, hc01, hc34, hlam, hphi, ht12, ht23, p141_1]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h104, hlam, p141_1]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    rcases p141_3 (m.d 0 4) (by simp) with h158 | h158
                    · linarith only [h158, h18, hlam]
                    · linarith only [h158, h32, hlam]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h32, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u4ehi4]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h0, h32, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u4ehi4]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h18, hc02, hc34, hlam, hphi, ht23, p141_1]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    rcases p141_3 (m.d 0 4) (by simp) with h165 | h165
                    · linarith only [h0, h104, h165, h33, hlam]
                    · linarith only [h165, h32, hlam]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h32, hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h103, hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h139, hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [h140, hlam, p141_0]
                  · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                    linarith only [hlam, p141_0]
                · linarith only [h0, h104, h140, h32, h33, hlam]
              · linarith only [h0, h139, h32, h33, hlam]
          · linarith only [h0, h103, h32, hlam]
      · linarith only [h32, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB0_M_IR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h0ehi := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h1, h10, h13, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h13, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h0, h12, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h10, h11, h5, hlam, hphi, ht45, u4ehi3, u5elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h1, h10, h18, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                            · rcases h4bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h1, h20, h4, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h1, h20, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h1, h10, h20, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                rcases p22_3 (m.d 0 4) (by simp) with h27 | h27
                                · rcases p22_3 (m.d 1 4) (by simp) with h28 | h28
                                  · linarith only [h0, h28, hlam]
                                  · linarith only [h28, h9, hlam]
                                · linarith only [h27, hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h0, hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h20, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h0, h10, h20, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h2, hlam, p22_1]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h7, hlam, p22_1]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h10, hlam, p22_1]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h4, hlam, p22_1]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h8, hlam, p22_1]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h1, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi2]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h1, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h6, hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h9, hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h20, hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [h21, hlam, p22_0]
                              · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                linarith only [hlam, p22_0]
                            · linarith only [h21, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h0, h20, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h6, h9, hlam, hphi, ht45, u4ehi1, u5elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                      · linarith only [h1, h55, h56, h8, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h1, h4, h56, h58, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
                            · rcases h4bigk with h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h1, h4, h55, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi4]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h1, h4, h60, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi4]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h1, h4, h55, h8, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi4]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                rcases p62_3 (m.d 0 4) (by simp) with h67 | h67
                                · rcases p62_3 (m.d 1 4) (by simp) with h68 | h68
                                  · linarith only [h0, h68, hlam]
                                  · linarith only [h55, h68, hlam]
                                · linarith only [h67, hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h0, hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p62_1, u4ehi4]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h8, hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h1, h4, h8, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi4]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h2, hlam, p62_1]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h7, hlam, p62_1]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h56, hlam, p62_1]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi4]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h4, hlam, p62_1]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h1, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi1]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h1, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi2]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h1, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p62_1, u4ehi4]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h6, hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h55, hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h60, hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [h61, hlam, p62_0]
                              · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                                linarith only [hlam, p62_0]
                            · linarith only [h61, h8, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h1, h4, h55, h60, h8, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h55, hlam, hphi, ht45, u4ehi1, u5elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                            · linarith only [h1, h100, h97, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h100, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h7, h96, h99, hlam]
                        · linarith only [h7, h97, h98, hlam, hphi, ht45, u4ehi1, u5elo3]
                      · linarith only [h7, h95, h97, hlam]
                    · linarith only [h96, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                      · linarith only [h1, h107, h108, h95, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                        · linarith only [h1, h108, h110, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                            · rcases h4bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h1, h107, h4, hc02, hlam, hphi, ht0b, ht5b, p114_1, u5ehi9]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h1, h107, h4, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p114_1, u4ehi4]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h1, h107, h4, h95, hc02, hlam, hphi, ht0b, ht45, ht5b, p114_1, u4ehi4]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                rcases p114_3 (m.d 0 4) (by simp) with h119 | h119
                                · rcases p114_3 (m.d 1 4) (by simp) with h120 | h120
                                  · linarith only [h0, h120, hlam]
                                  · linarith only [h107, h120, hlam]
                                · linarith only [h119, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h0, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h7, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h95, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p114_1, u4ehi4]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h2, hlam, p114_1]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p114_1, u4ehi1]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h108, hlam, p114_1]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h1, h108, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p114_1, u4ehi4]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h4, hlam, p114_1]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h1, h107, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p114_1, u4ehi4]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h1, h4, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h1, h4, hc02, hlam, hphi, ht0b, ht45, ht5b, p114_1, u4ehi4]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h6, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h107, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h112, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [h113, hlam, p114_0]
                              · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                                linarith only [hlam, p114_0]
                            · linarith only [h113, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h107, h112, h7, hlam]
                    · linarith only [h107, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h6, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
            · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
              · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                  · linarith only [h149, h152, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                      · linarith only [h149, h155, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h159 | h159
                            · rcases h4bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h151, h155, h157, h159, hc04, hlam, hphi, ht0b, ht45, ht5b, p160_1, u4ehi4]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h0, h155, h157, h159, hc01, hlam, hphi, ht0b, ht45, ht5b, p160_1, u4ehi4]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h4, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                rcases p160_3 (m.d 0 4) (by simp) with h165 | h165
                                · rcases p160_3 (m.d 1 4) (by simp) with h166 | h166
                                  · linarith only [h0, h166, hlam]
                                  · linarith only [h154, h166, hlam]
                                · linarith only [h165, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h0, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h155, h157, h159, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p160_1, u4ehi4]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h152, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p160_1, u4ehi4]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h2, hlam, p160_1]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h151, hlam, p160_1]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h155, hlam, p160_1]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h151, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p160_1, u4ehi4]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p160_1, u0ehi3]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h154, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p160_1, u4ehi4]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h155, h157, h159, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p160_1, u4ehi4]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                rcases p160_3 (m.d 0 4) (by simp) with h184 | h184
                                · linarith only [h184, h4, hlam]
                                · linarith only [h150, h184, hlam]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h150, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h154, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h158, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [h159, hlam, p160_0]
                              · obtain ⟨p160_0, p160_1, p160_2, p160_3⟩ := h160c
                                linarith only [hlam, p160_0]
                            · linarith only [h159, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h0, h154, h155, h157, h158, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h149, h157, h4, hc23, hc34, hlam, hphi]
                    · linarith only [h150, h154, hlam, hphi, ht45, u4ehi1, u5elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                  · linarith only [h149, h196, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                      · linarith only [h149, h199, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                            · rcases h4bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h198, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p204_1, u4ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h199, h201, h203, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p204_1, u4ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h4, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                rcases p204_3 (m.d 0 4) (by simp) with h209 | h209
                                · rcases p204_3 (m.d 1 4) (by simp) with h210 | h210
                                  · linarith only [h0, h210, hlam]
                                  · linarith only [h198, h210, hlam]
                                · linarith only [h209, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h0, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h151, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h196, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p204_1, u4ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h2, hlam, p204_1]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p204_1, u4ehi1]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h199, hlam, p204_1]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p204_1, u4ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p204_1, u0ehi3]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h198, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p204_1, u4ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h151, hc12, hc34, hlam, hphi, ht23, p204_1]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                rcases p204_3 (m.d 0 4) (by simp) with h228 | h228
                                · linarith only [h228, h4, hlam]
                                · linarith only [h150, h228, hlam]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h150, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h198, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h202, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h203, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                            · linarith only [h203, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h151, h198, h202, hlam]
                        · linarith only [h149, h201, h4, hc23, hc34, hlam, hphi]
                    · linarith only [h198, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h150, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h149, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h243 | h243
        · rcases m.htr 0 3 4 (by decide) (by decide) with h244 | h244
          · linarith only [h1, h2, h244, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
            · rcases m.htr 0 4 5 (by decide) (by decide) with h247 | h247
              · rcases m.htr 1 2 4 (by decide) (by decide) with h248 | h248
                · linarith only [h2, h243, h248, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                  · linarith only [h244, h246, h250, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h244, h246, h253, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
                        · linarith only [h1, h2, h255, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · linarith only [h1, h2, h246, h253, h255, hc23, hc34, hlam, hphi]
                    · linarith only [h252, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h1, h2, h246, h247, hlam, hphi, u5ehi8, u5elo4]
            · linarith only [h246, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
        · linarith only [h243, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h262 | h262
      · rcases m.htr 0 2 5 (by decide) (by decide) with h263 | h263
        · rcases m.htr 0 3 4 (by decide) (by decide) with h264 | h264
          · rcases m.htr 0 3 5 (by decide) (by decide) with h265 | h265
            · rcases m.htr 0 4 5 (by decide) (by decide) with h266 | h266
              · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                · rcases m.htr 1 3 4 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h271 | h271
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                          · linarith only [h1, h262, h272, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h272, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h0, h1, h262, h269, h271, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h1, h262, h270, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h1, h262, h266, h269, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                      · linarith only [h1, h262, h268, h278, h279, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1, h262, h279, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h1, h262, h266, h278, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1, h262, h267, hc12, hc23, hlam, hphi]
              · linarith only [h266, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h265, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · linarith only [h1, h262, h264, hlam]
        · linarith only [h262, h263, hlam, hphi, ht45, u4ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h288 | h288
        · rcases m.htr 0 3 4 (by decide) (by decide) with h289 | h289
          · rcases m.htr 0 3 5 (by decide) (by decide) with h290 | h290
            · rcases m.htr 0 4 5 (by decide) (by decide) with h291 | h291
              · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
                · linarith only [h262, h288, h292, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h294 | h294
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                            · rcases h4bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h294, h299, hc04, hlam, hphi, ht0b, ht45, ht5b, p300_1, u4ehi4]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h262, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h1, h289, h299, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p300_1, u4ehi4]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                rcases p300_3 (m.d 0 4) (by simp) with h305 | h305
                                · rcases p300_3 (m.d 1 4) (by simp) with h306 | h306
                                  · linarith only [h0, h306, hlam]
                                  · linarith only [h295, h306, hlam]
                                · linarith only [h305, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h0, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h292, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h299, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p300_1, u4ehi4]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p300_1, u4ehi4]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h296, hc23, hlam, hphi, ht01, ht12, p300_1, u0ehi3]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h294, h296, h299, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p300_1, u4ehi4]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h296, h299, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p300_1, u4ehi4]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                rcases p300_3 (m.d 0 4) (by simp) with h319 | h319
                                · linarith only [h262, h319, hlam]
                                · linarith only [h291, h319, hlam]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h289, hlam, p300_1]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h294, hlam, p300_1]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h296, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h294, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p300_1, u4ehi4]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h291, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h295, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h298, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [h299, hlam, p300_0]
                              · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                linarith only [hlam, p300_0]
                            · linarith only [h299, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h262, h288, h295, h298, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                        · linarith only [h262, h288, h296, h297, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h1, h288, h296, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h295, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h337 | h337
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h338 | h338
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h340 | h340
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
                            · rcases h4bigk with h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h1, h289, h337, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p342_1, u4ehi4]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h262, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h1, h289, h294, h337, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p342_1, u4ehi4]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                rcases p342_3 (m.d 0 4) (by simp) with h347 | h347
                                · rcases p342_3 (m.d 1 4) (by simp) with h348 | h348
                                  · linarith only [h0, h348, hlam]
                                  · linarith only [h337, h348, hlam]
                                · linarith only [h347, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h0, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h292, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h294, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p342_1, u4ehi4]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [hc24, hlam, hphi, ht01, ht12, p342_1, u0ehi3]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h337, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p342_1, u4ehi4]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h294, h337, h338, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p342_1, u4ehi4]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                rcases p342_3 (m.d 0 4) (by simp) with h361 | h361
                                · linarith only [h262, h361, hlam]
                                · linarith only [h291, h361, hlam]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h289, hlam, p342_1]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h337, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p342_1, u4ehi4]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h338, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h1, h289, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p342_1, u4ehi4]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h291, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h337, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h340, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [h341, hlam, p342_0]
                              · obtain ⟨p342_0, p342_1, p342_2, p342_3⟩ := h342c
                                linarith only [hlam, p342_0]
                            · linarith only [h294, h341, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h340, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h1, h289, h294, h337, h339, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                      · linarith only [h1, h289, h338, hlam]
                    · linarith only [h337, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h291, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h290, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
            · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
              · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                · linarith only [h262, h288, h383, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h385 | h385
                  · linarith only [h1, h288, h289, h385, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h387 | h387
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                      · linarith only [h1, h288, h289, h388, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · linarith only [h1, h288, h388, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h387, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h1, h288, h289, h382, hlam, hphi, u5ehi7, u5elo4]
            · linarith only [h1, h288, h381, hlam, hphi, u5ehi7, u5elo3]
        · linarith only [h288, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h395 | h395
    · rcases m.htr 0 2 4 (by decide) (by decide) with h396 | h396
      · rcases m.htr 0 2 5 (by decide) (by decide) with h397 | h397
        · rcases m.htr 0 3 4 (by decide) (by decide) with h398 | h398
          · rcases m.htr 0 3 5 (by decide) (by decide) with h399 | h399
            · rcases m.htr 0 4 5 (by decide) (by decide) with h400 | h400
              · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
                · rcases m.htr 1 3 4 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h405 | h405
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                            · linarith only [h395, h404, h407, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h407, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h403, h406, hlam, hphi, ht45, u4ehi2, u5elo1]
                        · linarith only [h399, h404, h405, hlam, hphi, ht45, u4ehi3, u5elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h412 | h412
                        · linarith only [h398, h404, h412, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h415 | h415
                            · rcases h4bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h0, hlam, p416_1]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h414, hc04, hlam, hphi, ht0b, ht45, ht5b, p416_1, u4ehi4]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h0, h401, h404, h414, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p416_1, u4ehi4]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                rcases p416_3 (m.d 0 4) (by simp) with h421 | h421
                                · rcases p416_3 (m.d 1 4) (by simp) with h422 | h422
                                  · rcases p416_3 (m.d 2 4) (by simp) with h423 | h423
                                    · linarith only [h396, h423, hlam]
                                    · linarith only [h414, h423, hlam]
                                  · linarith only [h403, h422, hlam]
                                · linarith only [h421, hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h401, hc12, hlam, hphi, ht01, p416_1, u0ehi3]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h401, h414, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p416_1, u4ehi4]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h401, h404, h414, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p416_1, u4ehi4]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                rcases p416_3 (m.d 0 4) (by simp) with h432 | h432
                                · linarith only [h0, h432, hlam]
                                · linarith only [h400, h432, hlam]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h396, hlam, p416_1]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h401, hlam, p416_1]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h404, hlam, p416_1]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h396, hc02, hlam, hphi, ht0b, ht45, ht5b, p416_1, u4ehi4]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h398, hlam, p416_1]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h402, hlam, p416_1]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h395, h398, hc02, hlam, hphi, ht0b, ht45, ht5b, p416_1, u4ehi2]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h395, h398, hc02, hlam, hphi, ht0b, ht45, ht5b, p416_1, u4ehi4]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h400, hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h403, hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h414, hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [h415, hlam, p416_0]
                              · obtain ⟨p416_0, p416_1, p416_2, p416_3⟩ := h416c
                                linarith only [hlam, p416_0]
                            · linarith only [h415, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h400, h414, hlam, hphi, ht45, u4ehi2, u5elo0]
                    · linarith only [h0, h400, h403, hlam, hphi, ht45, u4ehi0, u5elo0]
                  · linarith only [h0, h395, h398, h402, hc02, hlam, hphi, u0ehi0]
                · linarith only [h0, h396, h401, hc02, hlam, hphi, u0ehi0]
              · linarith only [h400, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h399, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
            · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
                · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                  · linarith only [h398, h457, h460, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h462 | h462
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h463 | h463
                      · linarith only [h398, h457, h463, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h465 | h465
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h466 | h466
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h467 | h467
                            · rcases h4bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h0, hlam, p468_1]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h463, h465, h467, hc04, hlam, hphi, ht0b, ht45, ht5b, p468_1, u4ehi4]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h398, hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                rcases p468_3 (m.d 0 4) (by simp) with h473 | h473
                                · rcases p468_3 (m.d 1 4) (by simp) with h474 | h474
                                  · rcases p468_3 (m.d 2 4) (by simp) with h475 | h475
                                    · linarith only [h396, h475, hlam]
                                    · linarith only [h466, h475, hlam]
                                  · linarith only [h462, h474, hlam]
                                · linarith only [h473, hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h460, hc34, hlam, hphi, ht01, ht12, ht23, p468_1, u0ehi3]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h460, h463, h465, h467, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p468_1, u4ehi4]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h460, hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                rcases p468_3 (m.d 0 4) (by simp) with h484 | h484
                                · linarith only [h0, h484, hlam]
                                · linarith only [h458, h484, hlam]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h396, hlam, p468_1]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h459, hlam, p468_1]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h463, hlam, p468_1]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h396, hc02, hlam, hphi, ht0b, ht45, ht5b, p468_1, u4ehi4]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p468_1, u0ehi3]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h0, hc34, hlam, hphi, ht01, ht12, ht23, p468_1, u0ehi0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h463, h465, h467, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p468_1, u4ehi4]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                rcases p468_3 (m.d 0 4) (by simp) with h496 | h496
                                · linarith only [h398, h496, hlam]
                                · linarith only [h458, h496, hlam]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h458, hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h462, hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h466, hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [h467, hlam, p468_0]
                              · obtain ⟨p468_0, p468_1, p468_2, p468_3⟩ := h468c
                                linarith only [hlam, p468_0]
                            · linarith only [h460, h467, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h458, h463, h465, h466, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h398, h457, h465, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h458, h462, hlam, hphi, ht45, u4ehi0, u5elo0]
                · linarith only [h0, h396, h459, hc02, hlam, hphi, u0ehi0]
              · linarith only [h458, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h457, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
        · linarith only [h397, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h512 | h512
        · rcases m.htr 0 3 4 (by decide) (by decide) with h513 | h513
          · linarith only [h395, h396, h513, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h515 | h515
            · rcases m.htr 0 4 5 (by decide) (by decide) with h516 | h516
              · rcases m.htr 1 2 4 (by decide) (by decide) with h517 | h517
                · linarith only [h395, h396, h515, h517, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
                  · linarith only [h513, h515, h519, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                      · linarith only [h513, h515, h522, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                        · linarith only [h395, h396, h524, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · linarith only [h395, h396, h515, h522, h524, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h516, h521, hc04, hlam, hphi, u0ehi0]
              · linarith only [h516, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h515, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
        · linarith only [h512, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h531 | h531
      · rcases m.htr 0 2 5 (by decide) (by decide) with h532 | h532
        · rcases m.htr 0 3 4 (by decide) (by decide) with h533 | h533
          · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
            · rcases m.htr 0 4 5 (by decide) (by decide) with h535 | h535
              · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                · rcases m.htr 1 3 4 (by decide) (by decide) with h537 | h537
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h538 | h538
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h539 | h539
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
                          · linarith only [h395, h531, h541, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h541, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h395, h532, h540, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h395, h532, h539, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h395, h531, h535, h538, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h533, h537, hc03, hlam, hphi, u0ehi0]
                · linarith only [h395, h531, h536, hc12, hc23, hlam, hphi]
              · linarith only [h535, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h534, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · linarith only [h395, h531, h533, hlam]
        · linarith only [h531, h532, hlam, hphi, ht45, u4ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h553 | h553
        · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
          · rcases m.htr 0 3 5 (by decide) (by decide) with h555 | h555
            · rcases m.htr 0 4 5 (by decide) (by decide) with h556 | h556
              · rcases m.htr 1 2 4 (by decide) (by decide) with h557 | h557
                · linarith only [h531, h553, h557, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h559 | h559
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h560 | h560
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h562 | h562
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h563 | h563
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                            · rcases h4bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h0, hlam, p565_1]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h531, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h564, hc04, hlam, hphi, ht0b, ht45, ht5b, p565_1, u4ehi4]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                rcases p565_3 (m.d 0 4) (by simp) with h570 | h570
                                · rcases p565_3 (m.d 1 4) (by simp) with h571 | h571
                                  · rcases p565_3 (m.d 2 4) (by simp) with h572 | h572
                                    · rcases p565_3 (m.d 3 4) (by simp) with h573 | h573
                                      · linarith only [h554, h573, hlam]
                                      · linarith only [h564, h573, hlam]
                                    · linarith only [h563, h572, hlam]
                                  · linarith only [h560, h571, hlam]
                                · linarith only [h570, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h559, hc13, hlam, hphi, ht01, p565_1, u0ehi3]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h557, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h557, h564, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u4ehi4]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                rcases p565_3 (m.d 0 4) (by simp) with h583 | h583
                                · linarith only [h0, h583, hlam]
                                · linarith only [h556, h583, hlam]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h531, h553, h561, h562, h564, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u4ehi4]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h0, h561, hc23, hlam, hphi, ht01, ht12, p565_1, u0ehi0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h561, h564, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u4ehi4]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                rcases p565_3 (m.d 0 4) (by simp) with h590 | h590
                                · linarith only [h531, h590, hlam]
                                · linarith only [h556, h590, hlam]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h554, hlam, p565_1]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h559, hlam, p565_1]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h561, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h554, hc03, hlam, hphi, ht0b, ht45, ht5b, p565_1, u4ehi4]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h556, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h560, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h563, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [h564, hlam, p565_0]
                              · obtain ⟨p565_0, p565_1, p565_2, p565_3⟩ := h565c
                                linarith only [hlam, p565_0]
                            · linarith only [h564, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h557, h563, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h531, h555, h561, h562, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                      · linarith only [h395, h553, h561, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h0, h556, h560, hc04, hlam, hphi, u0ehi0]
                  · linarith only [h0, h554, h559, hc03, hlam, hphi, u0ehi0]
              · linarith only [h556, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h531, h553, h554, h555, hlam, hphi, u5ehi7, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h611 | h611
            · rcases m.htr 0 4 5 (by decide) (by decide) with h612 | h612
              · rcases m.htr 1 2 4 (by decide) (by decide) with h613 | h613
                · linarith only [h531, h553, h613, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h615 | h615
                  · linarith only [h554, h611, h615, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h617 | h617
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h618 | h618
                      · linarith only [h395, h553, h554, h618, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · linarith only [h395, h553, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h0, h612, h617, hc04, hlam, hphi, u0ehi0]
              · linarith only [h612, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h395, h553, h611, hlam, hphi, u5ehi7, u5elo3]
        · linarith only [h553, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]

theorem n7l_sAB0_M_LI_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h0elo := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h5 | h5
    · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
      · rcases p0_3 (m.d 2 4) (by simp) with h7 | h7
        · rcases p0_3 (m.d 3 4) (by simp) with h8 | h8
          · rcases p0_3 (m.d 4 5) (by simp) with h9 | h9
            · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h6, hlam]
                · linarith only [h11, h12, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h6, hlam]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h18, h7, hlam]
                    · linarith only [h17, h18, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h21 | h21
                    · linarith only [h21, h7, hlam]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
                        · linarith only [h24, h8, hlam]
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                                      · linarith only [h17, h23, h24, h27, h32, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h17, h23, h29, h32, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h21, h28, h31, hlam, p0_1]
                                  · linarith only [h24, h29, h30, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                                · linarith only [h17, h23, h27, h29, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                              · linarith only [h11, h28, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                              · linarith only [h21, h27, h39, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                              · linarith only [h11, h39, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                          · linarith only [h26, hlam, p0_0]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
                        · linarith only [h43, h8, hlam]
                        · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
                          · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                              · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                                · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                      · linarith only [h43, h46, h51, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                                      · linarith only [h17, h51, hc02, hlam, hphi, ht23, ht34, u4elo3]
                                    · linarith only [h21, h47, h50, hlam, p0_1]
                                  · linarith only [h43, h48, h49, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                                · linarith only [h11, h17, h46, h48, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                              · linarith only [h11, h47, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                            · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                              · linarith only [h21, h46, h58, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                              · linarith only [h11, h58, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                          · linarith only [h45, hlam, p0_0]
          · linarith only [h8, hc34, hlam, hphi, p0_1, u4elo0]
        · linarith only [h7, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h6, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h5, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · rcases p0_3 (m.d 3 4) (by simp) with h73 | h73
          · rcases p0_3 (m.d 4 5) (by simp) with h74 | h74
            · linarith only [h74, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
                · linarith only [h77, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h70, h77, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
                · linarith only [h76, h80, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h70, h80, hlam]
          · linarith only [h73, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h70, h72, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h91 | h91
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · linarith only [h95, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h97 | h97
              · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
                · linarith only [h92, h98, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h97, h98, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h92, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h104 | h104
                    · linarith only [h104, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h104, h91, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h107 | h107
                    · linarith only [h103, h107, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                    · linarith only [h107, h91, hlam]
          · linarith only [h94, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h93, hlam, p0_0]
      · linarith only [h91, h92, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h91, hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
    · rcases p0_3 (m.d 1 4) (by simp) with h119 | h119
      · rcases p0_3 (m.d 2 4) (by simp) with h120 | h120
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h124 | h124
              · rcases m.htr 0 1 4 (by decide) (by decide) with h125 | h125
                · linarith only [h119, h125, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h124, h125, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h128 | h128
                · linarith only [h119, h128, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h131 | h131
                    · linarith only [h120, h131, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h130, h131, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h134 | h134
                    · linarith only [h120, h134, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h136 | h136
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h137 | h137
                        · linarith only [h137, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h118, h137, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h140 | h140
                        · linarith only [h140, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                        · linarith only [h118, h140, hlam]
          · linarith only [h121, hlam, p0_0]
        · linarith only [h120, hc24, hlam, hphi, p0_1, u4elo3]
      · linarith only [h119, hc14, hlam, hphi, p0_1, u4elo3]
    · linarith only [h118, hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h5 | h5
    · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
      · rcases p0_3 (m.d 2 4) (by simp) with h7 | h7
        · rcases p0_3 (m.d 3 4) (by simp) with h8 | h8
          · rcases p0_3 (m.d 4 5) (by simp) with h9 | h9
            · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h6, hlam]
                · linarith only [h11, h12, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h6, hlam]
                · linarith only [h15, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
          · linarith only [h8, hc34, hlam, hphi, p0_1, u4elo0]
        · linarith only [h6, h7, hc24, hlam, hphi, p0_1, u4elo1]
      · linarith only [h6, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h5, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h26 | h26
    · rcases p0_3 (m.d 1 4) (by simp) with h27 | h27
      · rcases p0_3 (m.d 2 4) (by simp) with h28 | h28
        · rcases p0_3 (m.d 3 4) (by simp) with h29 | h29
          · rcases p0_3 (m.d 4 5) (by simp) with h30 | h30
            · linarith only [h30, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 2 3 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                          · linarith only [h28, h38, hlam]
                          · linarith only [h35, h37, h38, hc23, hlam, hphi, ht34, u4elo0]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                          · linarith only [h28, h41, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                            · linarith only [h29, h43, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                                · linarith only [h32, h34, h43, h46, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                · linarith only [h37, h46, hc12, hlam, hphi, ht23, ht34, u4elo3]
                              · linarith only [h45, hlam, p0_0]
                      · linarith only [h36, hc04, hlam, hphi, p0_1, u4elo1]
                    · linarith only [h35, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h52 | h52
                    · linarith only [h28, h34, h52, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                    · linarith only [h52, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
                · linarith only [h26, h33, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h56 | h56
                · linarith only [h32, h56, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h26, h56, hlam]
          · linarith only [h29, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h28, hc24, hlam, hphi, p0_1, u4elo1]
      · linarith only [h27, hlam, p0_0]
    · linarith only [h26, hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h67 | h67
    · rcases p0_3 (m.d 1 4) (by simp) with h68 | h68
      · rcases p0_3 (m.d 2 4) (by simp) with h69 | h69
        · rcases p0_3 (m.d 3 4) (by simp) with h70 | h70
          · rcases p0_3 (m.d 4 5) (by simp) with h71 | h71
            · linarith only [h71, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
              · rcases m.htr 0 1 4 (by decide) (by decide) with h74 | h74
                · rcases m.htr 0 2 3 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                          · linarith only [h73, h79, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                          · linarith only [h68, h79, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                          · linarith only [h73, h75, h78, h82, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                          · linarith only [h68, h82, hlam]
                      · linarith only [h77, hc04, hlam, hphi, p0_1, u4elo2]
                    · linarith only [h67, h76, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
                    · linarith only [h75, h87, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                    · linarith only [h67, h87, hlam]
                · linarith only [h74, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h91 | h91
                · linarith only [h68, h73, h91, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h91, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
          · linarith only [h70, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h69, hlam, p0_0]
      · linarith only [h68, hc14, hlam, hphi, p0_1, u4elo2]
    · linarith only [h67, hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h102 | h102
    · rcases p0_3 (m.d 1 4) (by simp) with h103 | h103
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · rcases p0_3 (m.d 4 5) (by simp) with h106 | h106
            · linarith only [h106, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 1 4 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 2 3 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                          · linarith only [h104, h108, h114, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                          · linarith only [h113, h114, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                          · linarith only [h104, h110, h113, h117, hc03, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                            · linarith only [h108, h110, h113, h119, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                            · linarith only [h103, h119, hlam]
                      · linarith only [h112, hc04, hlam, hphi, p0_1, u4elo3]
                    · linarith only [h110, h111, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h104, h110, h124, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                    · linarith only [h124, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
                · linarith only [h109, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h128 | h128
                · linarith only [h103, h108, h128, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                · linarith only [h128, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
          · linarith only [h105, hlam, p0_0]
        · linarith only [h104, hc24, hlam, hphi, p0_1, u4elo3]
      · linarith only [h102, h103, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h102, hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi3, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h0elo := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h5 | h5
    · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
      · rcases p0_3 (m.d 2 4) (by simp) with h7 | h7
        · rcases p0_3 (m.d 3 4) (by simp) with h8 | h8
          · rcases p0_3 (m.d 4 5) (by simp) with h9 | h9
            · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h6, hlam]
                  · linarith only [h11, h13, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h6, hlam]
                  · linarith only [h11, h16, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h19 | h19
                · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h20, h6, hlam]
                  · linarith only [h19, h20, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, h6, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h26 | h26
                      · linarith only [h26, h7, hlam]
                      · linarith only [h25, h26, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h29 | h29
                      · linarith only [h29, h7, hlam]
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
                          · linarith only [h32, h8, hlam]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                                      · linarith only [h11, h25, h32, h35, h39, hc01, hc12, hlam, hphi]
                                      · linarith only [h25, h31, h37, h39, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h29, h36, h38, hlam, p0_1]
                                  · linarith only [h19, h37, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                                · linarith only [h11, h36, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                                · linarith only [h29, h35, h45, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                                · linarith only [h11, h45, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                            · linarith only [h34, hlam, p0_0]
                        · linarith only [h31, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h7, h8, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h7, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h6, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h5, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
    · rcases p0_3 (m.d 1 4) (by simp) with h59 | h59
      · rcases p0_3 (m.d 2 4) (by simp) with h60 | h60
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · rcases p0_3 (m.d 4 5) (by simp) with h62 | h62
            · linarith only [h62, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h64 | h64
              · rcases m.htr 0 1 3 (by decide) (by decide) with h65 | h65
                · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
                  · linarith only [h66, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h58, h66, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
                  · linarith only [h65, h69, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h58, h69, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                  · linarith only [h73, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h58, h73, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
                  · linarith only [h64, h76, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                  · linarith only [h58, h76, hlam]
          · linarith only [h61, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h58, h60, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h59, hlam, p0_0]
    · linarith only [h58, hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h87 | h87
    · rcases p0_3 (m.d 1 4) (by simp) with h88 | h88
      · rcases p0_3 (m.d 2 4) (by simp) with h89 | h89
        · rcases p0_3 (m.d 3 4) (by simp) with h90 | h90
          · rcases p0_3 (m.d 4 5) (by simp) with h91 | h91
            · linarith only [h91, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h93 | h93
              · rcases m.htr 0 1 3 (by decide) (by decide) with h94 | h94
                · rcases m.htr 0 1 4 (by decide) (by decide) with h95 | h95
                  · linarith only [h88, h95, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h93, h95, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
                  · linarith only [h88, h98, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h93, h98, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h101 | h101
                · rcases m.htr 0 1 4 (by decide) (by decide) with h102 | h102
                  · linarith only [h102, h88, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h101, h102, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h105 | h105
                  · linarith only [h105, h88, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h108 | h108
                      · linarith only [h108, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                      · linarith only [h108, h87, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
                      · linarith only [h107, h111, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                      · linarith only [h111, h87, hlam]
          · linarith only [h90, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h89, hlam, p0_0]
      · linarith only [h88, hc14, hlam, hphi, p0_1, u4elo2]
    · linarith only [h87, hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h122 | h122
    · rcases p0_3 (m.d 1 4) (by simp) with h123 | h123
      · rcases p0_3 (m.d 2 4) (by simp) with h124 | h124
        · rcases p0_3 (m.d 3 4) (by simp) with h125 | h125
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h126, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h128 | h128
              · rcases m.htr 0 1 3 (by decide) (by decide) with h129 | h129
                · rcases m.htr 0 1 4 (by decide) (by decide) with h130 | h130
                  · linarith only [h123, h130, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h129, h130, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h133 | h133
                  · linarith only [h123, h133, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h128, h133, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h136 | h136
                · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
                  · linarith only [h123, h137, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · linarith only [h136, h137, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h140 | h140
                  · linarith only [h123, h140, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h142 | h142
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h143 | h143
                      · linarith only [h124, h143, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                      · linarith only [h142, h143, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h146 | h146
                      · linarith only [h124, h146, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h149 | h149
                          · linarith only [h149, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                          · linarith only [h122, h149, hlam]
                        · linarith only [h128, h148, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h125, hlam, p0_0]
        · linarith only [h122, h124, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h122, h123, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h122, hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h5 | h5
    · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
      · rcases p0_3 (m.d 2 4) (by simp) with h7 | h7
        · rcases p0_3 (m.d 3 4) (by simp) with h8 | h8
          · rcases p0_3 (m.d 4 5) (by simp) with h9 | h9
            · linarith only [h9, hlam, p0_0]
            · rcases h5bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc15, hlam, hphi, p11_1, u5elo0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc25, hlam, hphi, p11_1, u5elo0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc35, hlam, hphi, p11_1, u5elo0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc45, hlam, hphi, p11_1, u5elo0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc05, hlam, hphi, p11_1, u5elo1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc25, hlam, hphi, p11_1, u5elo1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc35, hlam, hphi, p11_1, u5elo1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc45, hlam, hphi, p11_1, u5elo1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc05, hlam, hphi, p11_1, u5elo2]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc15, hlam, hphi, p11_1, u5elo2]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc35, hlam, hphi, p11_1, u5elo2]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc45, hlam, hphi, p11_1, u5elo2]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc05, hlam, hphi, p11_1, u5elo3]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc15, hlam, hphi, p11_1, u5elo3]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc25, hlam, hphi, p11_1, u5elo3]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc45, hlam, hphi, p11_1, u5elo3]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc05, hlam, hphi, p11_1, u5elo4]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p11_1, u4elo0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p11_1, u4elo0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p11_1, u4elo0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
          · linarith only [h8, hc34, hlam, hphi, p0_1, u4elo0]
        · linarith only [h7, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h6, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h5, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
    · rcases p0_3 (m.d 1 4) (by simp) with h46 | h46
      · rcases p0_3 (m.d 2 4) (by simp) with h47 | h47
        · rcases p0_3 (m.d 3 4) (by simp) with h48 | h48
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · linarith only [h49, hlam, p0_0]
            · rcases h5bigk with h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hlam, p51_0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc15, hlam, hphi, p51_1, u5elo0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc25, hlam, hphi, p51_1, u5elo0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc35, hlam, hphi, p51_1, u5elo0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc45, hlam, hphi, p51_1, u5elo0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc05, hlam, hphi, p51_1, u5elo1]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hlam, p51_0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc25, hlam, hphi, p51_1, u5elo1]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc35, hlam, hphi, p51_1, u5elo1]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc45, hlam, hphi, p51_1, u5elo1]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc05, hlam, hphi, p51_1, u5elo2]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc15, hlam, hphi, p51_1, u5elo2]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hlam, p51_0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc35, hlam, hphi, p51_1, u5elo2]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc45, hlam, hphi, p51_1, u5elo2]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc05, hlam, hphi, p51_1, u5elo3]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc15, hlam, hphi, p51_1, u5elo3]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc25, hlam, hphi, p51_1, u5elo3]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hlam, p51_0]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc45, hlam, hphi, p51_1, u5elo3]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc05, hlam, hphi, p51_1, u5elo4]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p51_1, u4elo1]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p51_1, u4elo1]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p51_1, u4elo1]
              · obtain ⟨p51_0, p51_1, p51_2, p51_3⟩ := h51c
                linarith only [hlam, p51_0]
          · linarith only [h48, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h47, hc24, hlam, hphi, p0_1, u4elo1]
      · linarith only [h46, hlam, p0_0]
    · linarith only [h45, hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h85 | h85
    · rcases p0_3 (m.d 1 4) (by simp) with h86 | h86
      · rcases p0_3 (m.d 2 4) (by simp) with h87 | h87
        · rcases p0_3 (m.d 3 4) (by simp) with h88 | h88
          · rcases p0_3 (m.d 4 5) (by simp) with h89 | h89
            · linarith only [h89, hlam, p0_0]
            · rcases h5bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hlam, p91_0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc15, hlam, hphi, p91_1, u5elo0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc25, hlam, hphi, p91_1, u5elo0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc35, hlam, hphi, p91_1, u5elo0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc45, hlam, hphi, p91_1, u5elo0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc05, hlam, hphi, p91_1, u5elo1]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hlam, p91_0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc25, hlam, hphi, p91_1, u5elo1]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc35, hlam, hphi, p91_1, u5elo1]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc45, hlam, hphi, p91_1, u5elo1]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc05, hlam, hphi, p91_1, u5elo2]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc15, hlam, hphi, p91_1, u5elo2]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hlam, p91_0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc35, hlam, hphi, p91_1, u5elo2]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc45, hlam, hphi, p91_1, u5elo2]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc05, hlam, hphi, p91_1, u5elo3]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc15, hlam, hphi, p91_1, u5elo3]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc25, hlam, hphi, p91_1, u5elo3]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hlam, p91_0]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc45, hlam, hphi, p91_1, u5elo3]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc05, hlam, hphi, p91_1, u5elo4]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p91_1, u4elo2]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p91_1, u4elo2]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p91_1, u4elo2]
              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                linarith only [hlam, p91_0]
          · linarith only [h88, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h87, hlam, p0_0]
      · linarith only [h86, hc14, hlam, hphi, p0_1, u4elo2]
    · linarith only [h85, hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h125 | h125
    · rcases p0_3 (m.d 1 4) (by simp) with h126 | h126
      · rcases p0_3 (m.d 2 4) (by simp) with h127 | h127
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hlam, p0_0]
            · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hlam, p131_0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc15, hlam, hphi, p131_1, u5elo0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc25, hlam, hphi, p131_1, u5elo0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc35, hlam, hphi, p131_1, u5elo0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc45, hlam, hphi, p131_1, u5elo0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc05, hlam, hphi, p131_1, u5elo1]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hlam, p131_0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc25, hlam, hphi, p131_1, u5elo1]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc35, hlam, hphi, p131_1, u5elo1]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc45, hlam, hphi, p131_1, u5elo1]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc05, hlam, hphi, p131_1, u5elo2]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc15, hlam, hphi, p131_1, u5elo2]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hlam, p131_0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc35, hlam, hphi, p131_1, u5elo2]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc45, hlam, hphi, p131_1, u5elo2]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc05, hlam, hphi, p131_1, u5elo3]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc15, hlam, hphi, p131_1, u5elo3]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc25, hlam, hphi, p131_1, u5elo3]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hlam, p131_0]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc45, hlam, hphi, p131_1, u5elo3]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc05, hlam, hphi, p131_1, u5elo4]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p131_1, u4elo3]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p131_1, u4elo3]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, p131_1, u4elo3]
              · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                linarith only [hlam, p131_0]
          · linarith only [h128, hlam, p0_0]
        · linarith only [h127, hc24, hlam, hphi, p0_1, u4elo3]
      · linarith only [h126, hc14, hlam, hphi, p0_1, u4elo3]
    · linarith only [h125, hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
