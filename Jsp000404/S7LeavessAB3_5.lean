import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB3_H_I_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h3elo := hb3.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · linarith only [h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h10 | h10
              · rcases m.htr 0 2 4 (by decide) (by decide) with h11 | h11
                · linarith only [h11, h5, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h13, h6, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h10, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h17 | h17
          · linarith only [h17, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h19 | h19
            · linarith only [h19, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
              · rcases m.htr 0 2 4 (by decide) (by decide) with h22 | h22
                · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h17, h22, h23, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h21, h22, h5, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h21, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h29 | h29
    · rcases p0_3 (m.d 1 4) (by simp) with h30 | h30
      · rcases p0_3 (m.d 2 4) (by simp) with h31 | h31
        · linarith only [h31, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h33 | h33
          · linarith only [h33, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h35, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h37 | h37
              · linarith only [h30, h37, hlam]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h39 | h39
                · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
                  · linarith only [h40, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h33, h39, h40, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h39, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · linarith only [h44, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h46 | h46
          · linarith only [h30, h46, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h48 | h48
            · linarith only [h30, h48, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h50 | h50
              · rcases m.htr 0 2 4 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h30, h52, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h46, h52, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h51, hlam, p0_0]
              · linarith only [h30, h50, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h29, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
    · rcases p0_3 (m.d 1 4) (by simp) with h59 | h59
      · rcases p0_3 (m.d 2 4) (by simp) with h60 | h60
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
              · linarith only [h59, h65, hlam]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h67 | h67
                · linarith only [h60, h67, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
                  · linarith only [h69, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h69, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · linarith only [h72, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h74 | h74
            · linarith only [h74, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h76 | h76
              · linarith only [h59, h76, hlam]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h78 | h78
                · rcases m.htr 0 3 4 (by decide) (by decide) with h79 | h79
                  · linarith only [h79, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h79, hlam, p0_0]
                · linarith only [h60, h78, hc02, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 2 4) (by simp) with h83 | h83
        · rcases p0_3 (m.d 3 4) (by simp) with h84 | h84
          · linarith only [h84, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h86 | h86
            · linarith only [h59, h86, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
              · rcases m.htr 0 2 4 (by decide) (by decide) with h89 | h89
                · linarith only [h83, h89, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
                  · linarith only [h59, h91, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h91, hlam, p0_0]
              · linarith only [h59, h88, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h95 | h95
          · linarith only [h95, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h97 | h97
            · linarith only [h59, h97, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h99 | h99
              · rcases m.htr 0 2 4 (by decide) (by decide) with h100 | h100
                · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h59, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h101, hlam, p0_0]
                · linarith only [h100, h83, h99, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h59, h99, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h58, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h107 | h107
    · rcases p0_3 (m.d 1 4) (by simp) with h108 | h108
      · rcases p0_3 (m.d 2 4) (by simp) with h109 | h109
        · rcases p0_3 (m.d 3 4) (by simp) with h110 | h110
          · linarith only [h110, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h112 | h112
            · linarith only [h112, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
              · linarith only [h108, h114, hlam]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h116 | h116
                · linarith only [h109, h116, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h118 | h118
                  · linarith only [h110, h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h110, h118, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · linarith only [h109, h121, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h125 | h125
              · linarith only [h108, h125, hlam]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h127 | h127
                · rcases m.htr 0 3 4 (by decide) (by decide) with h128 | h128
                  · linarith only [h109, h128, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h121, h127, h128, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h109, h125, h127, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 2 4) (by simp) with h132 | h132
        · rcases p0_3 (m.d 3 4) (by simp) with h133 | h133
          · linarith only [h108, h133, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
              · rcases m.htr 0 2 4 (by decide) (by decide) with h138 | h138
                · linarith only [h132, h138, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h140 | h140
                  · linarith only [h108, h140, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h133, h137, h140, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h108, h132, h137, hc01, hc24, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h144 | h144
          · linarith only [h108, h144, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h146 | h146
            · linarith only [h146, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h148 | h148
              · rcases m.htr 0 2 4 (by decide) (by decide) with h149 | h149
                · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
                  · linarith only [h108, h150, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h144, h148, h150, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h132, h148, h149, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h108, h148, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h107, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h156 | h156
    · linarith only [h156, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h158 | h158
      · rcases p0_3 (m.d 2 4) (by simp) with h159 | h159
        · rcases p0_3 (m.d 3 4) (by simp) with h160 | h160
          · linarith only [h160, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h162 | h162
            · linarith only [h162, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h164 | h164
              · linarith only [h164, hlam, p0_0]
              · linarith only [h164, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h167 | h167
          · linarith only [h167, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h169, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h171 | h171
              · linarith only [h171, hlam, p0_0]
              · linarith only [h171, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h158, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h176 | h176
    · rcases p0_3 (m.d 1 4) (by simp) with h177 | h177
      · rcases p0_3 (m.d 2 4) (by simp) with h178 | h178
        · linarith only [h178, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h180 | h180
          · linarith only [h180, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h182 | h182
            · linarith only [h182, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h184 | h184
              · linarith only [h184, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h176, h184, hlam]
      · linarith only [h177, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h188 | h188
      · rcases p0_3 (m.d 2 4) (by simp) with h189 | h189
        · linarith only [h189, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h191 | h191
          · linarith only [h191, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h193 | h193
            · linarith only [h193, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h195 | h195
              · linarith only [h195, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h176, h195, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h188, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h199 | h199
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h204, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h206 | h206
              · linarith only [h206, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h199, h206, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h211, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h213 | h213
              · linarith only [h213, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h199, h213, hlam]
      · linarith only [h200, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h217 | h217
      · rcases p0_3 (m.d 2 4) (by simp) with h218 | h218
        · rcases p0_3 (m.d 3 4) (by simp) with h219 | h219
          · linarith only [h219, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h223 | h223
              · linarith only [h223, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h199, h223, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h226 | h226
          · linarith only [h226, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h228 | h228
            · linarith only [h199, h228, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h230 | h230
              · linarith only [h199, h230, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h199, h230, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h217, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h234 | h234
    · rcases p0_3 (m.d 1 4) (by simp) with h235 | h235
      · rcases p0_3 (m.d 2 4) (by simp) with h236 | h236
        · rcases p0_3 (m.d 3 4) (by simp) with h237 | h237
          · linarith only [h237, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h239 | h239
            · linarith only [h239, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h241 | h241
              · linarith only [h237, h241, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h234, h241, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h244 | h244
          · linarith only [h236, h244, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h248 | h248
              · linarith only [h236, h248, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h234, h248, hlam]
      · linarith only [h235, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h252 | h252
      · rcases p0_3 (m.d 2 4) (by simp) with h253 | h253
        · rcases p0_3 (m.d 3 4) (by simp) with h254 | h254
          · linarith only [h234, h254, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h256 | h256
            · linarith only [h256, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h258 | h258
              · linarith only [h234, h258, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h234, h258, hc01, hc14, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h261 | h261
          · linarith only [h234, h261, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h263 | h263
            · linarith only [h263, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h265 | h265
              · linarith only [h234, h265, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h234, h265, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h252, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h269 | h269
    · linarith only [h269, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h271 | h271
      · rcases p0_3 (m.d 2 4) (by simp) with h272 | h272
        · rcases p0_3 (m.d 3 4) (by simp) with h273 | h273
          · linarith only [h273, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h275 | h275
            · linarith only [h275, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h277 | h277
              · linarith only [h271, h277, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h271, h277, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h281 | h281
        · rcases p0_3 (m.d 3 4) (by simp) with h282 | h282
          · linarith only [h282, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h284 | h284
            · linarith only [h284, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h286 | h286
              · rcases m.htr 0 2 4 (by decide) (by decide) with h287 | h287
                · linarith only [h287, hlam, p0_0]
                · linarith only [h287, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h271, h286, hlam]
        · linarith only [h281, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h292 | h292
    · rcases p0_3 (m.d 1 4) (by simp) with h293 | h293
      · linarith only [h293, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h295 | h295
        · rcases p0_3 (m.d 3 4) (by simp) with h296 | h296
          · linarith only [h296, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h298 | h298
            · linarith only [h298, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h300 | h300
              · rcases m.htr 0 2 4 (by decide) (by decide) with h301 | h301
                · linarith only [h301, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h292, h301, hlam]
              · linarith only [h300, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h295, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h306 | h306
      · linarith only [h306, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h308 | h308
        · rcases p0_3 (m.d 3 4) (by simp) with h309 | h309
          · linarith only [h292, h309, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h311 | h311
            · linarith only [h292, h311, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h313 | h313
              · linarith only [h292, h313, hlam]
              · linarith only [h313, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h308, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h318 | h318
    · rcases p0_3 (m.d 1 4) (by simp) with h319 | h319
      · rcases p0_3 (m.d 2 4) (by simp) with h320 | h320
        · rcases p0_3 (m.d 3 4) (by simp) with h321 | h321
          · linarith only [h321, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h323 | h323
            · linarith only [h323, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h325 | h325
              · linarith only [h319, h325, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h327 | h327
                · linarith only [h327, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h318, h327, hlam]
        · linarith only [h320, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h331 | h331
        · rcases p0_3 (m.d 3 4) (by simp) with h332 | h332
          · linarith only [h332, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h334 | h334
            · linarith only [h334, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h336 | h336
              · rcases m.htr 0 2 4 (by decide) (by decide) with h337 | h337
                · linarith only [h337, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h318, h337, hlam]
              · linarith only [h319, h336, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h331, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h342 | h342
      · rcases p0_3 (m.d 2 4) (by simp) with h343 | h343
        · rcases p0_3 (m.d 3 4) (by simp) with h344 | h344
          · linarith only [h344, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h346 | h346
            · linarith only [h318, h346, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h348 | h348
              · linarith only [h318, h342, h348, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h318, h342, h348, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h343, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h352 | h352
        · rcases p0_3 (m.d 3 4) (by simp) with h353 | h353
          · linarith only [h353, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h355 | h355
            · linarith only [h318, h355, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h357 | h357
              · rcases m.htr 0 2 4 (by decide) (by decide) with h358 | h358
                · linarith only [h318, h357, h358, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h318, h358, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h342, h357, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h352, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h363 | h363
    · rcases p0_3 (m.d 1 4) (by simp) with h364 | h364
      · rcases p0_3 (m.d 2 4) (by simp) with h365 | h365
        · rcases p0_3 (m.d 3 4) (by simp) with h366 | h366
          · linarith only [h366, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h368 | h368
            · linarith only [h368, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h370 | h370
              · linarith only [h364, h366, h370, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h372 | h372
                · linarith only [h366, h372, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h363, h372, hlam]
        · linarith only [h365, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h376 | h376
        · rcases p0_3 (m.d 3 4) (by simp) with h377 | h377
          · linarith only [h364, h377, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h379 | h379
            · linarith only [h379, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h381 | h381
              · rcases m.htr 0 2 4 (by decide) (by decide) with h382 | h382
                · linarith only [h364, h382, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h363, h382, hlam]
              · linarith only [h364, h381, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h376, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h387 | h387
      · rcases p0_3 (m.d 2 4) (by simp) with h388 | h388
        · rcases p0_3 (m.d 3 4) (by simp) with h389 | h389
          · linarith only [h363, h389, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h391 | h391
            · linarith only [h391, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h393 | h393
              · linarith only [h363, h387, h393, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h363, h387, h393, hc01, hc14, hlam, hphi, p0_1]
        · linarith only [h388, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h397 | h397
        · rcases p0_3 (m.d 3 4) (by simp) with h398 | h398
          · linarith only [h363, h398, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h400 | h400
            · linarith only [h400, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h402 | h402
              · rcases m.htr 0 2 4 (by decide) (by decide) with h403 | h403
                · linarith only [h363, h402, h403, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h363, h403, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h387, h402, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h397, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
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

theorem n7l_sAB3_H_I_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h3, h4, h6, h8, hlam]
              · linarith only [h3, h4, h8, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
            · linarith only [h13, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
              · linarith only [h13, h15, h3, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h15, h3, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
        · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h2, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h18, h19, h2, h21, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u3elo1, u5ehi3]
            · linarith only [h0, h18, h2, h21, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
          · linarith only [h18, h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
            · linarith only [h1, h26, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h0, h2, h26, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h30 | h30
    · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
        · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
            · linarith only [h30, h31, h34, h35, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · linarith only [h30, h31, h35, hc13, hlam, hphi, u3elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
            · linarith only [h30, h38, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h0, h30, h34, h38, hc13, hlam, hphi, u3elo4]
        · linarith only [h0, h30, h33, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h42 | h42
      · linarith only [h0, h42, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
        · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
          · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
            · linarith only [h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
            · linarith only [h30, h46, hc01, hlam, hphi, ht12, ht23, u3elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
            · linarith only [h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
            · linarith only [h30, h49, hc01, hlam, hphi, ht12, ht23, u3elo4]
        · linarith only [h0, h44, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem n7l_sAB3_H_I_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h5ehi := hb5.1
  have h3ehi := hb3.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
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
          · linarith only [h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h11 | h11
          · rcases p0_3 (m.d 4 5) (by simp) with h12 | h12
            · linarith only [h12, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h12, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h11, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h17 | h17
    · rcases p0_3 (m.d 1 4) (by simp) with h18 | h18
      · rcases p0_3 (m.d 2 4) (by simp) with h19 | h19
        · linarith only [h19, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · linarith only [h22, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h22, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h18, h21, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h18, h29, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h28, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
    · linarith only [h17, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
    · linarith only [h36, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h38 | h38
      · rcases p0_3 (m.d 2 4) (by simp) with h39 | h39
        · rcases p0_3 (m.d 3 4) (by simp) with h40 | h40
          · rcases p0_3 (m.d 4 5) (by simp) with h41 | h41
            · linarith only [h41, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h41, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h39, h40, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · rcases p0_3 (m.d 4 5) (by simp) with h46 | h46
            · linarith only [h46, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h46, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h45, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · linarith only [h38, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
    · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
      · rcases p0_3 (m.d 2 4) (by simp) with h54 | h54
        · linarith only [h54, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, h57, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h56, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h62 | h62
      · rcases p0_3 (m.d 2 4) (by simp) with h63 | h63
        · linarith only [h63, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h65 | h65
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · linarith only [h52, h66, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h66, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h65, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · linarith only [h62, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h73 | h73
    · linarith only [h73, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h75 | h75
      · rcases p0_3 (m.d 2 4) (by simp) with h76 | h76
        · rcases p0_3 (m.d 3 4) (by simp) with h77 | h77
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · linarith only [h78, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h78, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h77, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h76, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h83 | h83
        · rcases p0_3 (m.d 3 4) (by simp) with h84 | h84
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h85, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h83, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · rcases p0_3 (m.d 1 4) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · linarith only [h95, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h90, h95, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h94, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · linarith only [h100, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h102 | h102
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h103, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h102, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h114 | h114
      · rcases p0_3 (m.d 2 4) (by simp) with h115 | h115
        · rcases p0_3 (m.d 3 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 4 5) (by simp) with h117 | h117
            · linarith only [h117, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h117, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h116, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h122, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · rcases p0_3 (m.d 4 5) (by simp) with h128 | h128
            · linarith only [h128, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h126, h128, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h127, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · rcases p0_3 (m.d 4 5) (by simp) with h133 | h133
            · linarith only [h133, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h133, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h132, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h137 | h137
    · rcases p0_3 (m.d 1 4) (by simp) with h138 | h138
      · linarith only [h138, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, h142, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h151 | h151
      · linarith only [h151, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h153 | h153
        · rcases p0_3 (m.d 3 4) (by simp) with h154 | h154
          · rcases p0_3 (m.d 4 5) (by simp) with h155 | h155
            · linarith only [h137, h155, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, h155, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h137, h160, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h164 | h164
    · rcases p0_3 (m.d 1 4) (by simp) with h165 | h165
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h169, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h164, h169, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h168, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h173 | h173
        · linarith only [h173, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h165, h176, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h175, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h180 | h180
      · rcases p0_3 (m.d 2 4) (by simp) with h181 | h181
        · linarith only [h181, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h183 | h183
          · rcases p0_3 (m.d 4 5) (by simp) with h184 | h184
            · linarith only [h164, h184, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h180, h184, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h183, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h188 | h188
        · linarith only [h188, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h190 | h190
          · rcases p0_3 (m.d 4 5) (by simp) with h191 | h191
            · linarith only [h164, h191, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h191, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h190, hlam, p0_0]
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

theorem n7l_sAB3_H_I_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_H_I_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h5ehi := hb5.2.1
  have h3ehi := hb3.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
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
          · linarith only [h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h11 | h11
          · rcases p0_3 (m.d 4 5) (by simp) with h12 | h12
            · linarith only [h12, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h12, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h11, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h17 | h17
    · rcases p0_3 (m.d 1 4) (by simp) with h18 | h18
      · rcases p0_3 (m.d 2 4) (by simp) with h19 | h19
        · linarith only [h19, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · linarith only [h22, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h22, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h18, h21, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h18, h29, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h28, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
    · linarith only [h17, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
    · linarith only [h36, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h38 | h38
      · rcases p0_3 (m.d 2 4) (by simp) with h39 | h39
        · rcases p0_3 (m.d 3 4) (by simp) with h40 | h40
          · rcases p0_3 (m.d 4 5) (by simp) with h41 | h41
            · linarith only [h41, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h41, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h39, h40, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · rcases p0_3 (m.d 4 5) (by simp) with h46 | h46
            · linarith only [h46, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h46, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h45, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · linarith only [h38, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
    · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
      · rcases p0_3 (m.d 2 4) (by simp) with h54 | h54
        · linarith only [h54, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, h57, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h56, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h62 | h62
      · rcases p0_3 (m.d 2 4) (by simp) with h63 | h63
        · linarith only [h63, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h65 | h65
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · linarith only [h52, h66, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h66, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h65, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
      · linarith only [h62, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h73 | h73
    · linarith only [h73, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h75 | h75
      · rcases p0_3 (m.d 2 4) (by simp) with h76 | h76
        · rcases p0_3 (m.d 3 4) (by simp) with h77 | h77
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · linarith only [h78, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h78, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h77, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h76, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h83 | h83
        · rcases p0_3 (m.d 3 4) (by simp) with h84 | h84
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h85, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h83, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · rcases p0_3 (m.d 1 4) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · linarith only [h95, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h90, h95, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h94, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · linarith only [h100, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h102 | h102
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h103, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
        · linarith only [h102, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h114 | h114
      · rcases p0_3 (m.d 2 4) (by simp) with h115 | h115
        · rcases p0_3 (m.d 3 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 4 5) (by simp) with h117 | h117
            · linarith only [h117, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h117, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h116, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h122, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · rcases p0_3 (m.d 4 5) (by simp) with h128 | h128
            · linarith only [h128, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h126, h128, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h127, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · rcases p0_3 (m.d 4 5) (by simp) with h133 | h133
            · linarith only [h133, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h133, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h132, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h137 | h137
    · rcases p0_3 (m.d 1 4) (by simp) with h138 | h138
      · linarith only [h138, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, h142, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h151 | h151
      · linarith only [h151, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h153 | h153
        · rcases p0_3 (m.d 3 4) (by simp) with h154 | h154
          · rcases p0_3 (m.d 4 5) (by simp) with h155 | h155
            · linarith only [h137, h155, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, h155, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h137, h160, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h164 | h164
    · rcases p0_3 (m.d 1 4) (by simp) with h165 | h165
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h169, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h164, h169, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h168, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h173 | h173
        · linarith only [h173, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h165, h176, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h175, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h180 | h180
      · rcases p0_3 (m.d 2 4) (by simp) with h181 | h181
        · linarith only [h181, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h183 | h183
          · rcases p0_3 (m.d 4 5) (by simp) with h184 | h184
            · linarith only [h164, h184, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h180, h184, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h183, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h188 | h188
        · linarith only [h188, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h190 | h190
          · rcases p0_3 (m.d 4 5) (by simp) with h191 | h191
            · linarith only [h164, h191, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h191, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h190, hlam, p0_0]
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

theorem n7l_sAB3_H_I_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB3_H_I_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · rcases h4bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h0, h10, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h0, h7, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1, u3ehi3]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h0, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1, u3ehi3]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          rcases p11_3 (m.d 0 4) (by simp) with h16 | h16
                          · rcases p11_3 (m.d 1 4) (by simp) with h17 | h17
                            · rcases p11_3 (m.d 2 4) (by simp) with h18 | h18
                              · linarith only [h0, h18, hlam]
                              · linarith only [h18, h9, hlam]
                            · linarith only [h17, h6, hlam]
                          · linarith only [h16, hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h0, h8, h9, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u3ehi4]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h3, h8, h9, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u3ehi4]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h10, h3, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u3ehi4]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          rcases p11_3 (m.d 0 4) (by simp) with h27 | h27
                          · rcases p11_3 (m.d 1 4) (by simp) with h28 | h28
                            · rcases p11_3 (m.d 2 4) (by simp) with h29 | h29
                              · linarith only [h29, h3, hlam]
                              · linarith only [h29, h9, hlam]
                            · linarith only [h28, hlam, p11_0]
                          · linarith only [h0, h27, h3, h8, h9, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u3ehi4]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h0, hlam, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h3, hlam, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h0, h10, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1, u3ehi4]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h3, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h1, hlam, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h4, hlam, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h7, hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h1, hc03, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [hc04, hc45, hlam, hphi, p11_1]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h6, hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h9, hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [h10, hlam, p11_0]
                        · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                          linarith only [hlam, p11_0]
                      · linarith only [h10, h3, h9, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h6, h7, h9, hlam, hphi, ht34, ht45, u3ehi3, u5elo1]
                  · linarith only [h8, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                  · linarith only [h52, h7, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h52, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h4, h6, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
            · linarith only [h2, h5, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
            · linarith only [h4, h57, hc34, hlam, hphi, u3ehi4]
            · linarith only [h57, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
          · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
            · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
              · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                      · rcases h4bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h60, h66, hc04, hc45, hlam, hphi, ht0b, ht5b, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h3, h60, h66, hc04, hc45, hlam, hphi, ht0b, ht5b, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi3]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          rcases p67_3 (m.d 0 4) (by simp) with h72 | h72
                          · rcases p67_3 (m.d 1 4) (by simp) with h73 | h73
                            · linarith only [h0, h3, h73, hlam]
                            · linarith only [h62, h73, hlam]
                          · linarith only [h72, hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, h3, hlam, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h3, hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, h3, h66, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, hlam, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, h66, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h0, hc02, hc45, hlam, hphi, ht0b, ht5b, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h1, hlam, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h60, hlam, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h63, hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h60, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [hc04, hc45, hlam, hphi, p67_1]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h62, hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h65, hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [h66, hlam, p67_0]
                        · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                          linarith only [hlam, p67_0]
                      · linarith only [h0, h3, h62, h66, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h3, h62, h65, hlam]
                  · linarith only [h64, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h3, h60, h63, hlam]
              · linarith only [h60, h62, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
            · linarith only [h61, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
            · linarith only [h103, h60, hc34, hlam, hphi, u3ehi4]
            · linarith only [h103, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
      · linarith only [h1, h107, hc34, hlam, hphi, u3ehi4]
      · linarith only [h107, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
    · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
      · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
        · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
          · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
            · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
              · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                      · rcases h4bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h0, h112, hlam, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h0, hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h0, h112, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h0, h112, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h110, h113, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p120_1, u3ehi3]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h0, h113, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h113, h119, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          rcases p120_3 (m.d 0 4) (by simp) with h130 | h130
                          · linarith only [h0, h112, h130, hlam]
                          · linarith only [h110, h119, h130, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h110, h119, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h112, hlam, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h112, h119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p120_1, u3ehi4]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h112, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h110, hlam, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h113, hlam, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h116, hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h0, h110, h112, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [hc04, hc45, hlam, hphi, p120_1]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h115, hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h118, hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [h119, hlam, p120_0]
                        · obtain ⟨p120_0, p120_1, p120_2, p120_3⟩ := h120c
                          linarith only [hlam, p120_0]
                      · linarith only [h112, h118, h119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h118, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h116, h117, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h110, h116, hlam]
              · linarith only [h0, h110, h112, h115, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
            · linarith only [h111, h114, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
          · linarith only [h0, h110, h112, h113, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
          · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
            · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
              · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                      · rcases h4bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h0, h112, hc12, hc24, hlam, hphi, p162_1]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h0, hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h0, h161, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p162_1]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          rcases p162_3 (m.d 0 4) (by simp) with h167 | h167
                          · rcases p162_3 (m.d 1 4) (by simp) with h168 | h168
                            · rcases p162_3 (m.d 2 4) (by simp) with h169 | h169
                              · rcases p162_3 (m.d 3 4) (by simp) with h170 | h170
                                · linarith only [h110, h170, hlam]
                                · linarith only [h161, h170, hlam]
                              · linarith only [h160, h169, hlam]
                            · linarith only [h157, h168, hlam]
                          · linarith only [h167, hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h110, h155, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u3ehi3]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h112, hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h112, h158, h161, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p162_1, u3ehi4]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          rcases p162_3 (m.d 0 4) (by simp) with h180 | h180
                          · rcases p162_3 (m.d 1 4) (by simp) with h181 | h181
                            · rcases p162_3 (m.d 2 4) (by simp) with h182 | h182
                              · rcases p162_3 (m.d 3 4) (by simp) with h183 | h183
                                · linarith only [h155, h183, hlam]
                                · linarith only [h161, h183, hlam]
                              · linarith only [h160, h182, hlam]
                            · linarith only [h181, hlam, p162_0]
                          · linarith only [h110, h112, h158, h161, h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p162_1, u3ehi4]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h110, h158, h161, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p162_1, u3ehi4]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h112, h158, hc12, hc23, hlam, hphi, p162_1]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h158, h161, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p162_1, u3ehi4]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          rcases p162_3 (m.d 0 4) (by simp) with h193 | h193
                          · linarith only [h0, h193, hlam]
                          · linarith only [h110, h161, h193, hlam]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h110, hlam, p162_1]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h155, hlam, p162_1]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h158, hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h110, hc03, hc45, hlam, hphi, ht0b, ht5b, p162_1]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [hc04, hc45, hlam, hphi, p162_1]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h157, hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h160, hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [h161, hlam, p162_0]
                        · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                          linarith only [hlam, p162_0]
                      · linarith only [h157, h161, hlam, hphi, ht34, ht45, u3ehi3, u5elo1]
                    · linarith only [h0, h157, h160, hc02, hlam, hphi, ht23, ht34, ht45, u5elo1]
                  · linarith only [h159, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h0, h110, h158, hlam]
              · linarith only [h155, h157, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
            · linarith only [h156, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h212 | h212
            · linarith only [h155, h212, hc34, hlam, hphi, u3ehi4]
            · linarith only [h212, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
      · linarith only [h111, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h216 | h216
      · linarith only [h110, h216, hc34, hlam, hphi, u3ehi4]
      · linarith only [h216, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem n7l_sAB3_H_I_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3elo := hb3.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · linarith only [h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h11 | h11
          · linarith only [h11, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h13 | h13
            · linarith only [h13, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h13, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h17 | h17
    · rcases p0_3 (m.d 1 4) (by simp) with h18 | h18
      · rcases p0_3 (m.d 2 4) (by simp) with h19 | h19
        · linarith only [h19, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h21 | h21
          · linarith only [h21, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h23 | h23
            · linarith only [h23, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h23, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h28 | h28
          · linarith only [h18, h28, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h30 | h30
            · linarith only [h18, h30, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h30, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h17, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · rcases p0_3 (m.d 1 4) (by simp) with h35 | h35
      · rcases p0_3 (m.d 2 4) (by simp) with h36 | h36
        · rcases p0_3 (m.d 3 4) (by simp) with h37 | h37
          · linarith only [h37, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h39 | h39
            · linarith only [h39, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h39, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h42 | h42
          · linarith only [h42, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h44 | h44
            · linarith only [h36, h44, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h44, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h47 | h47
        · rcases p0_3 (m.d 3 4) (by simp) with h48 | h48
          · linarith only [h48, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h50 | h50
            · linarith only [h35, h50, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h50, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h53 | h53
          · linarith only [h53, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h55 | h55
            · linarith only [h47, h55, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h55, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h34, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h60 | h60
    · linarith only [h60, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h62 | h62
      · rcases p0_3 (m.d 2 4) (by simp) with h63 | h63
        · rcases p0_3 (m.d 3 4) (by simp) with h64 | h64
          · linarith only [h64, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · linarith only [h66, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h66, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h69 | h69
          · linarith only [h69, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h71 | h71
            · linarith only [h71, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h71, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h62, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
    · rcases p0_3 (m.d 1 4) (by simp) with h77 | h77
      · rcases p0_3 (m.d 2 4) (by simp) with h78 | h78
        · linarith only [h78, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h80 | h80
          · linarith only [h80, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h82 | h82
            · linarith only [h82, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h76, h82, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h77, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h86 | h86
      · rcases p0_3 (m.d 2 4) (by simp) with h87 | h87
        · linarith only [h87, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h89 | h89
          · linarith only [h76, h89, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h91 | h91
            · linarith only [h76, h91, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h91, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h86, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h95 | h95
    · rcases p0_3 (m.d 1 4) (by simp) with h96 | h96
      · rcases p0_3 (m.d 2 4) (by simp) with h97 | h97
        · rcases p0_3 (m.d 3 4) (by simp) with h98 | h98
          · linarith only [h98, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h100 | h100
            · linarith only [h100, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h100, h95, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · linarith only [h103, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h105 | h105
            · linarith only [h105, h97, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h105, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h96, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h109 | h109
      · rcases p0_3 (m.d 2 4) (by simp) with h110 | h110
        · rcases p0_3 (m.d 3 4) (by simp) with h111 | h111
          · linarith only [h111, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h113 | h113
            · linarith only [h113, h95, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h113, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h116 | h116
          · linarith only [h116, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, h95, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h109, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h123 | h123
    · linarith only [h123, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h126, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h133 | h133
        · rcases p0_3 (m.d 3 4) (by simp) with h134 | h134
          · linarith only [h134, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h136 | h136
            · linarith only [h136, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h136, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h133, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h140 | h140
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · linarith only [h141, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h143 | h143
        · rcases p0_3 (m.d 3 4) (by simp) with h144 | h144
          · linarith only [h144, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h146 | h146
            · linarith only [h146, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h140, h146, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h143, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · linarith only [h150, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h152 | h152
        · rcases p0_3 (m.d 3 4) (by simp) with h153 | h153
          · linarith only [h140, h153, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h155 | h155
            · linarith only [h140, h155, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h155, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h152, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · rcases p0_3 (m.d 2 4) (by simp) with h162 | h162
        · rcases p0_3 (m.d 3 4) (by simp) with h163 | h163
          · linarith only [h163, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h162, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h169 | h169
        · rcases p0_3 (m.d 3 4) (by simp) with h170 | h170
          · linarith only [h170, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h172 | h172
            · linarith only [h161, h172, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h172, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h169, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h176 | h176
      · rcases p0_3 (m.d 2 4) (by simp) with h177 | h177
        · rcases p0_3 (m.d 3 4) (by simp) with h178 | h178
          · linarith only [h178, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h180 | h180
            · linarith only [h160, h180, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, h180, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h177, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h184 | h184
        · rcases p0_3 (m.d 3 4) (by simp) with h185 | h185
          · linarith only [h185, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h187 | h187
            · linarith only [h176, h187, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h187, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h184, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3, u5ehi9]
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

theorem n7l_sAB3_H_I_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_H_I_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3ehi := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · rcases h4bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, h3, hc03, hlam, hphi, ht0b, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, h4, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p8_1, u3ehi3]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p8_1, u3ehi3]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, hc03, hlam, hphi, ht0b, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, h7, hc14, hlam, hphi, ht01, ht0b, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h4, h7, hc14, hlam, hphi, ht01, ht0b, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h7, hc14, hlam, hphi, ht01, ht0b, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, hlam, p8_1]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h4, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8_1, u5ehi9]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h2, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h3, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h6, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h7, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                · linarith only [h7, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h2, h4, h6, hlam, hphi, ht34, ht45, u3ehi3, u5elo0]
            · linarith only [h1, h5, hlam, hphi, ht34, ht45, u3ehi2, u5elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
            · linarith only [h37, h4, hc34, hlam, hphi, u3ehi4]
            · linarith only [h37, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
          · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
            · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
              · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                · rcases h4bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    rcases p44_3 (m.d 0 4) (by simp) with h46 | h46
                    · rcases p44_3 (m.d 1 4) (by simp) with h47 | h47
                      · linarith only [h47, hlam, p44_0]
                      · rcases p44_3 (m.d 2 4) (by simp) with h49 | h49
                        · rcases p44_3 (m.d 3 4) (by simp) with h50 | h50
                          · linarith only [h0, h50, hlam]
                          · linarith only [h3, h40, h43, h49, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u5ehi6]
                        · linarith only [h3, h40, h43, h49, hlam]
                    · linarith only [h46, hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h3, h40, h43, hc04, hlam, hphi, ht0b, ht5b, p44_1, u5ehi6]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h0, h3, h43, hc03, hlam, hphi, ht0b, ht5b, p44_1, u5ehi6]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h0, h3, hc03, hlam, hphi, ht0b, ht5b, p44_1, u5ehi6]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h3, h40, h43, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h3, h40, h43, hlam, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h3, h43, hlam, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h3, hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h0, h3, h43, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    rcases p44_3 (m.d 0 4) (by simp) with h64 | h64
                    · rcases p44_3 (m.d 1 4) (by simp) with h65 | h65
                      · linarith only [h65, hlam, p44_0]
                      · rcases p44_3 (m.d 2 4) (by simp) with h67 | h67
                        · rcases p44_3 (m.d 3 4) (by simp) with h68 | h68
                          · linarith only [h40, h68, hlam]
                          · linarith only [h3, h43, h68, hlam]
                        · linarith only [h67, hlam, p44_0]
                    · linarith only [h0, h3, h43, h64, hlam]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h3, h40, h43, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h3, h40, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h0, hlam, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h0, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h40, hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h0, h3, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h2, hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [hc14, hc45, hlam, hphi, p44_1]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h42, hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [h43, hlam, p44_0]
                  · obtain ⟨p44_0, p44_1, p44_2, p44_3⟩ := h44c
                    linarith only [hlam, p44_0]
                · linarith only [h2, h43, hlam, hphi, ht34, ht45, u3ehi3, u5elo0]
              · linarith only [h2, h40, h42, hlam, hphi, ht34, ht45, u3ehi3, u5elo0]
            · linarith only [h1, h41, hlam, hphi, ht34, ht45, u3ehi2, u5elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
            · linarith only [h40, h89, hc34, hlam, hphi, u3ehi4]
            · linarith only [h89, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · linarith only [h0, h2, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h94 | h94
    · linarith only [h0, h94, hc34, hlam, hphi, u3ehi4]
    · linarith only [h94, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem n7l_sAB3_H_L_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5emin := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · rcases h5emin with h5 | h5 | h5 | h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
            · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
            · linarith only [h3, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
            · linarith only [h2, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
          · linarith only [h0, h4, hc34, hlam, hphi, u4elo0]
        · linarith only [h0, h3, hc24, hlam, hphi, u4elo0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
        · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
          · linarith only [h14, h2, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h14, hc34, hlam, hphi, u4elo0]
        · linarith only [h0, h13, hc24, hlam, hphi, u4elo0]
    · linarith only [h0, h1, hc14, hlam, hphi, u4elo0]
  · linarith only [h0, hc04, hlam, hphi, u4elo4]

theorem n7l_sAB3_H_L_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h3bigk := hb3.1
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
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h14, h15, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                · linarith only [h15, hc34, hlam, hphi, u4elo4]
                              · linarith only [h14, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h13, hc14, hlam, hphi, u4elo4]
                          · linarith only [h12, h7, h8, hc13, hlam, hphi, ht34, u4elo0]
                        · linarith only [h11, h9, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h10, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                · linarith only [h0, h23, h27, h28, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                · linarith only [h28, hc34, hlam, hphi, u4elo4]
                              · linarith only [h27, h9, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h26, hc14, hlam, hphi, u4elo4]
                          · linarith only [h23, h25, h7, h8, h9, hc24, hlam, hphi, u4elo0]
                        · linarith only [h23, h24, h9, hc24, hlam, hphi, u4elo3]
                      · linarith only [h23, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h8, hc04, hlam, hphi, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
                  · linarith only [h37, h6, h7, hc34, hlam, hphi, u4elo0]
                  · linarith only [h37, hc04, hlam, hphi, u4elo4]
              · linarith only [h6, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h5, hc02, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h42 | h42
            · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
                · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                    · linarith only [h0, h4, h42, h46, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                                · rcases h3bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h46, h48, h52, h53, hc03, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h4, hlam, p54_1]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    rcases p54_3 (m.d 0 3) (by simp) with h58 | h58
                                    · rcases p54_3 (m.d 1 3) (by simp) with h59 | h59
                                      · linarith only [h1, h59, hlam]
                                      · linarith only [h49, h59, hlam]
                                    · linarith only [h58, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    rcases p54_3 (m.d 0 3) (by simp) with h63 | h63
                                    · rcases p54_3 (m.d 1 3) (by simp) with h64 | h64
                                      · linarith only [h1, h64, hlam]
                                      · linarith only [h50, h64, hlam]
                                    · linarith only [h63, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h1, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h46, hlam, p54_1]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h1, h53, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    rcases p54_3 (m.d 0 3) (by simp) with h72 | h72
                                    · rcases p54_3 (m.d 1 3) (by simp) with h73 | h73
                                      · rcases p54_3 (m.d 2 3) (by simp) with h74 | h74
                                        · rcases p54_3 (m.d 3 4) (by simp) with h75 | h75
                                          · linarith only [h49, h75, hlam]
                                          · linarith only [h53, h75, hlam]
                                        · linarith only [h1, h4, h74, hlam, p54_1]
                                      · linarith only [h73, hlam, p54_0]
                                    · linarith only [h44, h72, hlam]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h0, h4, h48, h52, h53, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p54_1]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h46, h48, h52, h53, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p54_1]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    rcases p54_3 (m.d 0 3) (by simp) with h84 | h84
                                    · linarith only [h4, h84, hlam]
                                    · linarith only [h43, h84, hlam]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    rcases p54_3 (m.d 0 3) (by simp) with h87 | h87
                                    · linarith only [h4, h87, hlam]
                                    · linarith only [h44, h87, hlam]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h43, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h49, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h52, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h52, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p54_1, u4elo2]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h44, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h50, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h4, hc02, hc35, hlam, hphi, ht23, p54_1]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [h53, hlam, p54_0]
                                  · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                    linarith only [hlam, p54_0]
                                · linarith only [h2, h51, h53, hc34, hlam, hphi, u4elo0]
                              · linarith only [h0, h4, h48, h52, hc24, hlam, hphi, u4elo3]
                            · linarith only [h49, h51, hc34, hlam, hphi, u4elo4]
                          · linarith only [h44, h45, h50, hc13, hlam, hphi, ht34, u4elo0]
                        · linarith only [h46, h48, h49, hc24, hlam, hphi, u4elo3]
                      · linarith only [h48, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h45, hc04, hlam, hphi, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
                  · linarith only [h107, h4, h42, h44, hc24, hlam, hphi, u4elo0]
                  · linarith only [h107, hc04, hlam, hphi, u4elo4]
              · linarith only [h4, h42, h43, hc24, hlam, hphi, u4elo3]
            · linarith only [h42, hc02, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h112 | h112
          · rcases m.htr 0 2 4 (by decide) (by decide) with h113 | h113
            · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
              · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
                · linarith only [h0, h112, h115, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h0, h117, h3, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h117, hc04, hlam, hphi, u4elo4]
              · linarith only [h114, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h113, hc02, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h122 | h122
            · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                · linarith only [h1, h124, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                  · linarith only [h0, h126, h3, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h126, hc04, hlam, hphi, u4elo4]
              · linarith only [h123, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h122, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h132 | h132
      · rcases m.htr 0 1 5 (by decide) (by decide) with h133 | h133
        · rcases m.htr 0 2 3 (by decide) (by decide) with h134 | h134
          · linarith only [h0, h1, h134, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h136 | h136
            · rcases m.htr 0 3 4 (by decide) (by decide) with h137 | h137
              · rcases m.htr 0 3 5 (by decide) (by decide) with h138 | h138
                · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                    · linarith only [h0, h1, h134, h140, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h147 | h147
                                · linarith only [h0, h1, h140, h142, h146, h147, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h132, h145, h147, hc34, hlam, hphi, u4elo0]
                              · linarith only [h0, h1, h140, h146, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h143, h145, hc34, hlam, hphi, u4elo4]
                          · linarith only [h0, h1, h142, h144, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h142, h143, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h142, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h139, hc04, hlam, hphi, u4elo4]
                · linarith only [h1, h133, h138, hlam]
              · linarith only [h0, h1, h137, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · linarith only [h136, hc02, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h159 | h159
          · linarith only [h0, h1, h159, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h161 | h161
            · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
              · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                  · linarith only [h0, h133, h164, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h164, hc04, hlam, hphi, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
                  · linarith only [h0, h1, h163, h167, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h167, hc04, hlam, hphi, u4elo4]
              · linarith only [h0, h1, h162, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · linarith only [h161, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h0, h132, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h173 | h173
    · rcases m.htr 0 1 4 (by decide) (by decide) with h174 | h174
      · rcases m.htr 0 1 5 (by decide) (by decide) with h175 | h175
        · rcases m.htr 0 2 3 (by decide) (by decide) with h176 | h176
          · rcases m.htr 0 2 4 (by decide) (by decide) with h177 | h177
            · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
              · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
                · rcases m.htr 0 4 5 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h182 | h182
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                · linarith only [h0, h173, h181, h186, h187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h187, hc34, hlam, hphi, u4elo4]
                              · linarith only [h186, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h185, hc14, hlam, hphi, u4elo4]
                          · linarith only [h0, h173, h179, h183, h184, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h183, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h182, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h173, h176, h178, h181, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h180, hc04, hlam, hphi, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h178, h179, h197, hc34, hlam, hphi, u4elo0]
                  · linarith only [h197, hc04, hlam, hphi, u4elo4]
              · linarith only [h178, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h177, hc02, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h0, h173, h176, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h203 | h203
          · rcases m.htr 0 2 4 (by decide) (by decide) with h204 | h204
            · rcases m.htr 0 3 4 (by decide) (by decide) with h205 | h205
              · rcases m.htr 0 3 5 (by decide) (by decide) with h206 | h206
                · linarith only [h173, h175, h206, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h208 | h208
                  · linarith only [h173, h175, h208, hc13, hlam, hphi, ht34, u4elo0]
                  · linarith only [h208, hc04, hlam, hphi, u4elo4]
              · linarith only [h205, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h173, h204, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h173, h203, hlam]
      · linarith only [h173, h174, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h215 | h215
      · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
        · rcases m.htr 0 2 3 (by decide) (by decide) with h217 | h217
          · rcases m.htr 0 2 4 (by decide) (by decide) with h218 | h218
            · rcases m.htr 0 3 4 (by decide) (by decide) with h219 | h219
              · rcases m.htr 0 3 5 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                                · rcases h3bigk with h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h173, hlam, p229_1]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h227, h228, hc03, hc45, hlam, hphi, ht0b, ht5b, p229_1]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    rcases p229_3 (m.d 0 3) (by simp) with h233 | h233
                                    · rcases p229_3 (m.d 1 3) (by simp) with h234 | h234
                                      · rcases p229_3 (m.d 2 3) (by simp) with h235 | h235
                                        · linarith only [h217, h235, hlam]
                                        · linarith only [h227, h235, hlam]
                                      · linarith only [h224, h234, hlam]
                                    · linarith only [h233, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    rcases p229_3 (m.d 0 3) (by simp) with h240 | h240
                                    · rcases p229_3 (m.d 1 3) (by simp) with h241 | h241
                                      · rcases p229_3 (m.d 2 3) (by simp) with h242 | h242
                                        · linarith only [h217, h242, hlam]
                                        · linarith only [h227, h228, h242, hlam]
                                      · linarith only [h225, h241, hlam]
                                    · linarith only [h240, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h173, h215, h223, h227, h228, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p229_1]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h222, h227, h228, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p229_1]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    rcases p229_3 (m.d 0 3) (by simp) with h250 | h250
                                    · linarith only [h173, h250, hlam]
                                    · linarith only [h219, h250, hlam]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    rcases p229_3 (m.d 0 3) (by simp) with h253 | h253
                                    · linarith only [h173, h253, hlam]
                                    · linarith only [h220, h253, hlam]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h217, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h222, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h217, h228, hc02, hc45, hlam, hphi, ht0b, ht5b, p229_1]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    rcases p229_3 (m.d 0 3) (by simp) with h260 | h260
                                    · rcases p229_3 (m.d 1 3) (by simp) with h261 | h261
                                      · rcases p229_3 (m.d 2 3) (by simp) with h262 | h262
                                        · rcases p229_3 (m.d 3 4) (by simp) with h263 | h263
                                          · linarith only [h227, h263, hlam]
                                          · linarith only [h228, h263, hlam]
                                        · linarith only [h262, hlam, p229_0]
                                      · linarith only [h225, h261, hlam]
                                    · linarith only [h220, h260, hlam]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h219, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h224, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h227, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h215, h223, h227, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p229_1, u4elo0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h220, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h225, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h220, h221, hc23, hlam, hphi, ht34, p229_1, u4elo0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [h228, hlam, p229_0]
                                  · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                                    linarith only [hlam, p229_0]
                                · linarith only [h215, h226, h228, hc34, hlam, hphi, u4elo0]
                              · linarith only [h227, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h226, hc14, hlam, hphi, u4elo4]
                          · linarith only [h173, h220, h225, hlam]
                        · linarith only [h173, h224, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h223, hc02, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h0, h215, h217, h222, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h221, hc04, hlam, hphi, u4elo4]
                · linarith only [h173, h216, h220, hlam]
              · linarith only [h173, h215, h219, hc14, hlam, hphi, u4elo3]
            · linarith only [h218, hc02, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h290 | h290
            · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
              · rcases m.htr 0 3 5 (by decide) (by decide) with h292 | h292
                · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                            · linarith only [h0, h215, h217, h294, h298, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h298, hc14, hlam, hphi, u4elo4]
                          · linarith only [h0, h215, h217, h292, h294, h295, h297, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h296, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h217, h294, h295, hc03, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
                            · linarith only [h0, h215, h294, h307, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h307, hc14, hlam, hphi, u4elo4]
                          · linarith only [h0, h216, h292, h294, h306, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h173, h305, hc03, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h215, h304, hc14, hlam, hphi, u4elo2]
                  · linarith only [h293, hc04, hlam, hphi, u4elo4]
                · linarith only [h0, h216, h217, h292, hlam]
              · linarith only [h0, h217, h291, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h215, h290, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h317 | h317
          · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
            · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
              · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
                · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                  · linarith only [h215, h216, h321, hc14, hlam, hphi, u4elo0]
                  · linarith only [h321, hc04, hlam, hphi, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                  · linarith only [h319, h320, h324, hc34, hlam, hphi, u4elo0]
                  · linarith only [h324, hc04, hlam, hphi, u4elo4]
              · linarith only [h173, h215, h319, hc14, hlam, hphi, u4elo3]
            · linarith only [h317, h318, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
            · rcases m.htr 0 3 4 (by decide) (by decide) with h330 | h330
              · rcases m.htr 0 3 5 (by decide) (by decide) with h331 | h331
                · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                  · linarith only [h215, h216, h332, hc14, hlam, hphi, u4elo0]
                  · linarith only [h332, hc04, hlam, hphi, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
                  · linarith only [h0, h215, h317, h331, h335, hc14, hlam, hphi, u4elo0]
                  · linarith only [h335, hc04, hlam, hphi, u4elo4]
              · linarith only [h0, h215, h317, h330, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h215, h329, hc14, hlam, hphi, u4elo2]
      · linarith only [h215, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB3_H_L_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h3, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h8, hc34, hlam, hphi, u4elo4]
                · linarith only [h7, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
              · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h15, h17, h19, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h19, hc34, hlam, hphi, u4elo4]
                · linarith only [h15, h17, h18, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · linarith only [h15, h17, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h15, h16, hc24, hlam, hphi, ht45, u5elo2]
          · linarith only [h15, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h28 | h28
    · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
            · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h0, h28, h30, h33, h35, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h35, hc34, hlam, hphi, u4elo4]
                · linarith only [h33, h34, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h33, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h32, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h28, h30, h31, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h30, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h28, h29, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
      · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
        · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
            · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
              · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                  · linarith only [h28, h44, h46, h48, h50, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h50, hc34, hlam, hphi, u4elo4]
                · linarith only [h28, h44, h46, h48, h49, hc23, hc34, hlam, hphi, ht45, u3elo1, u5elo3]
              · linarith only [h48, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h28, h44, h45, h46, h47, hc24, hlam, hphi, ht45, u5elo2]
          · linarith only [h28, h45, h46, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h44, h45, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
      · linarith only [h44, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB3_H_L_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h3bigk := hb3.1
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
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h11, hc34, hlam, hphi, u4elo4]
                      · linarith only [h10, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h9, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h4, h8, hc13, hlam, hphi, ht34, u4elo0]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h5, h6, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h0, h19, h22, h24, h3, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h24, hc34, hlam, hphi, u4elo4]
                      · linarith only [h23, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h19, h22, h5, hc24, hlam, hphi, u4elo3]
                  · linarith only [h19, h21, h4, h5, hc24, hlam, hphi, u4elo0]
                · linarith only [h19, h20, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h19, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h4, hc03, hlam, hphi, ht34, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
          · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
            · linarith only [h0, h3, h34, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
              · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                        · rcases h3bigk with h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h34, h36, h39, h41, hc03, hc45, hlam, hphi, ht0b, ht5b, p42_1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h3, hlam, p42_1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            rcases p42_3 (m.d 0 3) (by simp) with h46 | h46
                            · rcases p42_3 (m.d 1 3) (by simp) with h47 | h47
                              · linarith only [h1, h47, hlam]
                              · linarith only [h38, h47, hlam]
                            · linarith only [h46, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            rcases p42_3 (m.d 0 3) (by simp) with h51 | h51
                            · rcases p42_3 (m.d 1 3) (by simp) with h52 | h52
                              · linarith only [h1, h52, hlam]
                              · linarith only [h34, h36, h37, h39, h40, h41, h52, hc45, hlam, hphi, u5elo1]
                            · linarith only [h51, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h1, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h34, hlam, p42_1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h1, h41, hc01, hc45, hlam, hphi, ht0b, ht5b, p42_1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            rcases p42_3 (m.d 0 3) (by simp) with h60 | h60
                            · rcases p42_3 (m.d 1 3) (by simp) with h61 | h61
                              · rcases p42_3 (m.d 2 3) (by simp) with h62 | h62
                                · rcases p42_3 (m.d 3 4) (by simp) with h63 | h63
                                  · linarith only [h38, h63, hlam]
                                  · linarith only [h41, h63, hlam]
                                · linarith only [h40, h62, hlam]
                              · linarith only [h61, hlam, p42_0]
                            · linarith only [h0, h3, h36, h37, h39, h40, h41, h60, hc45, hlam, hphi, u5elo1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h0, h3, h36, h39, h41, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p42_1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h34, h36, h39, h41, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p42_1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            rcases p42_3 (m.d 0 3) (by simp) with h72 | h72
                            · linarith only [h3, h72, hlam]
                            · linarith only [h33, h72, hlam]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            rcases p42_3 (m.d 0 3) (by simp) with h75 | h75
                            · linarith only [h3, h75, hlam]
                            · linarith only [h0, h3, h36, h37, h39, h40, h41, h75, hc45, hlam, hphi, u5elo1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h33, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h38, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h39, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h39, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p42_1, u4elo2]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h3, hc02, hlam, hphi, ht23, ht34, ht45, p42_1, u5elo3]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h34, h36, h37, h39, h40, h41, hc45, hlam, hphi, p42_1, u5elo1]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h40, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [h41, hlam, p42_0]
                          · obtain ⟨p42_0, p42_1, p42_2, p42_3⟩ := h42c
                            linarith only [hlam, p42_0]
                        · linarith only [h41, hc34, hlam, hphi, u4elo4]
                      · linarith only [h40, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h3, h39, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h34, h36, h38, hc24, hlam, hphi, u4elo3]
                · linarith only [h36, h37, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h36, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h33, hc03, hlam, hphi, ht34, u4elo3]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h96 | h96
      · rcases m.htr 0 2 3 (by decide) (by decide) with h97 | h97
        · linarith only [h0, h1, h97, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h99 | h99
          · rcases m.htr 1 2 3 (by decide) (by decide) with h100 | h100
            · linarith only [h0, h1, h100, h97, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                        · linarith only [h0, h1, h100, h102, h105, h107, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h107, hc34, hlam, hphi, u4elo4]
                      · linarith only [h0, h1, h100, h106, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h100, h102, h105, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h102, h104, h99, hc24, hlam, hphi, u4elo0]
                · linarith only [h102, h103, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h102, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h0, h1, h99, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h96, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h117 | h117
    · rcases m.htr 0 1 4 (by decide) (by decide) with h118 | h118
      · rcases m.htr 0 2 3 (by decide) (by decide) with h119 | h119
        · rcases m.htr 0 3 4 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h0, h117, h121, h125, h127, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h127, hc34, hlam, hphi, u4elo4]
                      · linarith only [h126, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h125, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h120, h124, hc13, hlam, hphi, ht34, u4elo0]
                · linarith only [h0, h123, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h117, h121, h122, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h0, h117, h119, h121, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h120, hc03, hlam, hphi, ht34, u4elo3]
        · linarith only [h0, h117, h119, hlam]
      · linarith only [h117, h118, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h139 | h139
      · rcases m.htr 0 2 3 (by decide) (by decide) with h140 | h140
        · rcases m.htr 0 3 4 (by decide) (by decide) with h141 | h141
          · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
            · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
              · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                        · rcases h3bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h117, hlam, p149_1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h146, h148, hc03, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            rcases p149_3 (m.d 0 3) (by simp) with h153 | h153
                            · rcases p149_3 (m.d 1 3) (by simp) with h154 | h154
                              · rcases p149_3 (m.d 2 3) (by simp) with h155 | h155
                                · linarith only [h140, h155, hlam]
                                · linarith only [h146, h155, hlam]
                              · linarith only [h145, h154, hlam]
                            · linarith only [h153, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            rcases p149_3 (m.d 0 3) (by simp) with h160 | h160
                            · rcases p149_3 (m.d 1 3) (by simp) with h161 | h161
                              · rcases p149_3 (m.d 2 3) (by simp) with h162 | h162
                                · linarith only [h140, h162, hlam]
                                · linarith only [h147, h162, hlam]
                              · linarith only [h117, h139, h143, h144, h146, h147, h148, h161, hc45, hlam, hphi, u5elo1]
                            · linarith only [h160, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h117, h139, h143, h146, h148, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p149_1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h142, h146, h148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p149_1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            rcases p149_3 (m.d 0 3) (by simp) with h170 | h170
                            · linarith only [h117, h170, hlam]
                            · linarith only [h141, h170, hlam]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            rcases p149_3 (m.d 0 3) (by simp) with h173 | h173
                            · linarith only [h117, h173, hlam]
                            · linarith only [h117, h139, h143, h144, h146, h147, h148, h173, hc45, hlam, hphi, u5elo1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h140, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h142, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h140, h148, hc02, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            rcases p149_3 (m.d 0 3) (by simp) with h180 | h180
                            · rcases p149_3 (m.d 1 3) (by simp) with h181 | h181
                              · rcases p149_3 (m.d 2 3) (by simp) with h182 | h182
                                · rcases p149_3 (m.d 3 4) (by simp) with h183 | h183
                                  · linarith only [h146, h183, hlam]
                                  · linarith only [h148, h183, hlam]
                                · linarith only [h182, hlam, p149_0]
                              · linarith only [h0, h117, h139, h140, h143, h146, h148, h181, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p149_1]
                            · linarith only [h140, h180, hlam, p149_1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h141, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h145, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h146, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h117, h139, h143, h146, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p149_1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h117, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p149_1, u5elo3]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h144, h147, hc13, hlam, hphi, ht34, ht45, p149_1, u5elo1]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h147, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [h148, hlam, p149_0]
                          · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                            linarith only [hlam, p149_0]
                        · linarith only [h148, hc34, hlam, hphi, u4elo4]
                      · linarith only [h147, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h146, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h117, h141, h145, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                · linarith only [h0, h144, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h117, h142, h143, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h139, h140, h142, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h117, h139, h141, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h207 | h207
          · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
            · rcases m.htr 1 2 4 (by decide) (by decide) with h209 | h209
              · rcases m.htr 1 2 5 (by decide) (by decide) with h210 | h210
                · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h214 | h214
                        · linarith only [h0, h139, h140, h208, h209, h212, h214, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h214, hc34, hlam, hphi, u4elo4]
                      · linarith only [h0, h139, h140, h209, h213, hc24, hlam, hphi, ht45, u5elo3]
                    · linarith only [h0, h139, h140, h209, h212, hc24, hlam, hphi, u4elo3]
                  · linarith only [h0, h139, h140, h207, h208, h209, h211, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h139, h140, h208, h209, h210, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h140, h208, h209, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
              · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h0, h139, h208, h222, h225, h227, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h227, hc34, hlam, hphi, u4elo4]
                      · linarith only [h0, h139, h208, h222, h225, h226, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h139, h208, h222, h225, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h117, h207, h224, hc03, hlam, hphi, ht34, u4elo0]
                · linarith only [h0, h139, h222, h223, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h222, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h0, h139, h140, h207, hc14, hlam, hphi, u4elo3]
      · linarith only [h139, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB3_H_L_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB3_H_L_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
  · linarith only [h0, hc14, hlam, hphi, u4elo4]

theorem n7l_sAB3_H_L_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h3elo := hb3.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h3, h5, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h6, hc34, hlam, hphi, u4elo4]
            · linarith only [h5, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h4, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
            · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
              · linarith only [h11, h12, h13, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h13, hc34, hlam, hphi, u4elo4]
            · linarith only [h12, h3, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h11, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
    · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
      · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
            · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
              · linarith only [h0, h20, h22, h24, h25, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h25, hc34, hlam, hphi, u4elo4]
            · linarith only [h24, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h20, h22, h23, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h22, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h20, h21, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h32 | h32
      · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
        · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
            · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
              · linarith only [h20, h32, h34, h35, h36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
              · linarith only [h36, hc34, hlam, hphi, u4elo4]
            · linarith only [h35, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h20, h33, h34, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h32, h33, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
      · linarith only [h32, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB3_H_L_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB3_H_L_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB3_H_L_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB3_H_R_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h3elo := hb3.1
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi3]

theorem n7l_sAB3_H_R_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
      · linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · linarith only [h1, hc45, hlam, hphi, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB3_H_R_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h5bigk := hb5.1
  have h3ehi := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h10, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h10, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h8, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h14, h8, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h16, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h16, hc45, hlam, hphi, u4ehi2]
                · linarith only [h0, h2, h7, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h5, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, h5, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, h5, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h23, hc45, hlam, hphi, u4ehi1]
          · linarith only [h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                      · linarith only [h27, h3, h31, h33, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h27, h3, h30, h32, h33, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h31, h32, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h27, h3, h30, h31, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h30, hc45, hlam, hphi, u4ehi1]
              · linarith only [h28, h29, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
              · linarith only [h28, h40, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                · linarith only [h0, h28, h42, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h42, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
            · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
                        · linarith only [h0, h51, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h51, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h3, h47, h50, hlam]
                    · linarith only [h3, h46, h47, h48, h49, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h3, h47, h48, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h47, hc45, hlam, hphi, u4ehi1]
              · linarith only [h45, h46, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
              · linarith only [h45, h59, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                · linarith only [h0, h45, h61, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h61, hc45, hlam, hphi, u4ehi1]
      · linarith only [h2, hc45, hlam, hphi, u4ehi0]
    · linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h66 | h66
    · linarith only [h0, h66, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
      · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
        · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
          · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
            · linarith only [h0, h68, h71, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
              · linarith only [h66, h71, h73, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                  · linarith only [h0, h68, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h66, h69, h76, h78, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                      · linarith only [h69, h80, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h68, h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h0, h68, h75, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
          · linarith only [h69, h70, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
          · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
            · linarith only [h0, h68, h86, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
              · linarith only [h66, h86, h88, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h68, h91, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h66, h91, h93, hc34, hlam, hphi, u3ehi0]
                    · linarith only [h69, h85, h91, h93, hc34, hlam, hphi, u3ehi2]
                · linarith only [h68, h90, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
            · linarith only [h0, h68, h97, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
              · linarith only [h66, h68, h97, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                  · linarith only [h0, h102, h68, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h104 | h104
                    · linarith only [h102, h104, h66, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                        · rcases h5bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h66, h85, hc12, hc35, hlam, hphi, ht23, p108_1]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h101, h102, h68, h69, h85, hc04, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h66, hlam, p108_1]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h68, hc04, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h101, h102, h66, h69, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p108_1, u3ehi0, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h85, hlam, p108_1]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h99, hlam, p108_1]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h101, h102, h69, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h104, h107, h68, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h104, h107, h85, hc12, hc34, hlam, hphi, ht23, p108_1]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h104, hlam, p108_1]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h104, h107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h107, h68, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h101, h107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h107, h85, hc12, hc34, hlam, hphi, ht23, p108_1]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h68, hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h101, hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h106, hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [h107, hlam, p108_0]
                          · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                            linarith only [hlam, p108_0]
                        · linarith only [h102, h107, h69, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h101, h106, h69, hlam]
                · linarith only [h101, hc45, hlam, hphi, u4ehi1]
      · linarith only [h68, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB3_H_R_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi3]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
    · linarith only [h2, hc45, hlam, hphi, u4ehi2]

theorem n7l_sAB3_H_R_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h3bigk := hb3.1
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
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h7, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                    · linarith only [h11, h6, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h11, h13, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h11, h15, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h15, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                  · linarith only [h0, h20, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h22, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h22, h24, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                        · linarith only [h2, h26, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h26, hc45, hlam, hphi, u4ehi1]
            · linarith only [h4, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
            · linarith only [h30, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
              · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h33, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h33, h35, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                    · linarith only [h1, h37, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h1, h30, h39, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                        · linarith only [h2, h41, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h41, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                · linarith only [h3, h32, h4, h44, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                  · linarith only [h3, h32, h4, h46, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                    · linarith only [h3, h32, h4, h48, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h1, h3, h30, h32, h50, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                        · linarith only [h2, h52, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h52, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h55 | h55
          · rcases m.htr 0 3 5 (by decide) (by decide) with h56 | h56
            · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
              · linarith only [h0, h3, h57, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                · linarith only [h0, h3, h59, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                  · linarith only [h0, h3, h61, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                    · linarith only [h1, h63, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h3, h55, h63, h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                        · linarith only [h2, h67, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h67, hc45, hlam, hphi, u4ehi1]
            · linarith only [h55, h56, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h71 | h71
            · linarith only [h55, h71, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
              · linarith only [h0, h3, h73, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
                · linarith only [h0, h75, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h0, h3, h55, h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                    · linarith only [h1, h79, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                      · linarith only [h1, h81, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
                        · linarith only [h2, h83, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h83, hc45, hlam, hphi, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h86 | h86
        · rcases m.htr 0 3 4 (by decide) (by decide) with h87 | h87
          · linarith only [h1, h2, h87, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h89 | h89
            · linarith only [h0, h2, h86, h89, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
              · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                · linarith only [h0, h2, h92, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                  · linarith only [h0, h2, h92, h94, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                    · linarith only [h1, h2, h87, h92, h96, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h91, h96, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                · linarith only [h0, h2, h86, h91, h99, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h2, h86, h91, h99, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
          · linarith only [h1, h102, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
            · linarith only [h102, h104, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
              · linarith only [h0, h106, h2, h86, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                · linarith only [h0, h108, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
                  · linarith only [h1, h106, h108, h110, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                    · linarith only [h1, h102, h108, h112, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                      · linarith only [h1, h104, h112, h114, h2, hc03, hc34, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                          · linarith only [h1, h106, h112, h117, h2, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                            · linarith only [h114, h116, h117, h119, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                                · rcases h3bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h1, h106, h108, h2, hc12, hc24, hlam, hphi, p123_1]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h86, hlam, p123_1]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h102, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h104, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h1, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h106, hlam, p123_1]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h112, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h114, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h119, h122, hc03, hc34, hlam, hphi, p123_1]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h106, h119, h122, hc12, hc34, hlam, hphi, ht23, p123_1]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h117, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h119, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    rcases p123_3 (m.d 0 3) (by simp) with h139 | h139
                                    · linarith only [h139, hlam, p123_0]
                                    · rcases p123_3 (m.d 1 3) (by simp) with h141 | h141
                                      · linarith only [h112, h141, hlam]
                                      · rcases p123_3 (m.d 2 3) (by simp) with h143 | h143
                                        · linarith only [h117, h143, hlam]
                                        · linarith only [h143, h86, hlam]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    rcases p123_3 (m.d 0 3) (by simp) with h146 | h146
                                    · linarith only [h102, h146, hlam]
                                    · linarith only [h1, h146, hlam]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h0, h86, hc12, hc34, hlam, hphi, ht23, p123_1]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p123_1, u5ehi3]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    rcases p123_3 (m.d 0 3) (by simp) with h152 | h152
                                    · linarith only [h152, hlam, p123_0]
                                    · rcases p123_3 (m.d 1 3) (by simp) with h154 | h154
                                      · linarith only [h114, h154, hlam]
                                      · rcases p123_3 (m.d 2 3) (by simp) with h156 | h156
                                        · linarith only [h119, h156, hlam]
                                        · linarith only [h156, h86, hlam]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    rcases p123_3 (m.d 0 3) (by simp) with h159 | h159
                                    · linarith only [h104, h159, hlam]
                                    · linarith only [h1, h159, hlam]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h0, h86, hc12, hc35, hlam, hphi, ht23, p123_1]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [h122, hlam, p123_0]
                                  · obtain ⟨p123_0, p123_1, p123_2, p123_3⟩ := h123c
                                    linarith only [hlam, p123_0]
                                · linarith only [h108, h117, h122, hc45, hlam, hphi, u4ehi1]
                              · linarith only [h108, h116, h121, hlam]
                        · linarith only [h116, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h168 | h168
      · linarith only [h1, h168, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h170 | h170
        · linarith only [h0, h1, h170, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
          · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
            · rcases m.htr 1 2 3 (by decide) (by decide) with h174 | h174
              · linarith only [h0, h1, h170, h174, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h176 | h176
                · linarith only [h0, h1, h174, h176, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                  · linarith only [h0, h1, h174, h178, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                                · linarith only [h172, h186, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h186, hc45, hlam, hphi, u4ehi3]
                              · linarith only [h0, h168, h176, h178, h182, h185, hc12, hc25, hlam, hphi]
                            · linarith only [h1, h173, h174, h184, hlam]
                          · linarith only [h1, h172, h174, h183, hlam]
                        · linarith only [h182, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h1, h173, h181, hlam]
                    · linarith only [h1, h172, h180, hlam]
            · linarith only [h172, h173, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h196 | h196
            · linarith only [h172, h196, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
              · linarith only [h0, h1, h172, h198, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
                · linarith only [h0, h1, h172, h200, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h202 | h202
                  · linarith only [h0, h1, h172, h202, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h204 | h204
                    · linarith only [h0, h1, h172, h198, h204, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h204, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h207 | h207
    · rcases m.htr 0 1 4 (by decide) (by decide) with h208 | h208
      · linarith only [h0, h208, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h210 | h210
        · rcases m.htr 0 3 4 (by decide) (by decide) with h211 | h211
          · linarith only [h0, h207, h211, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h213 | h213
            · linarith only [h211, h213, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
              · rcases m.htr 1 2 4 (by decide) (by decide) with h216 | h216
                · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h218 | h218
                    · linarith only [h207, h208, h211, h216, h218, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                      · linarith only [h207, h208, h213, h218, h220, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                          · linarith only [h207, h208, h215, h218, h223, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                            · linarith only [h207, h208, h215, h218, h220, h225, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                              · linarith only [h216, h227, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h227, hc45, hlam, hphi, u4ehi2]
                        · linarith only [h207, h208, h222, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h216, h217, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                  · linarith only [h216, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                    · linarith only [h0, h207, h211, h216, h234, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h207, h216, h236, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                          · linarith only [h0, h207, h215, h216, h234, h238, h239, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h207, h216, h239, hc13, hc34, hlam, hphi]
                        · linarith only [h238, hc45, hlam, hphi, u4ehi1]
              · linarith only [h0, h207, h210, h215, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h207, h210, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h245 | h245
      · linarith only [h207, h245, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h247 | h247
        · rcases m.htr 0 3 4 (by decide) (by decide) with h248 | h248
          · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
            · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
              · rcases m.htr 1 2 4 (by decide) (by decide) with h251 | h251
                · rcases m.htr 1 2 5 (by decide) (by decide) with h252 | h252
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                          · linarith only [h247, h256, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                            · linarith only [h248, h256, h258, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                              · linarith only [h251, h260, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h260, hc45, hlam, hphi, u4ehi2]
                        · linarith only [h255, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h207, h248, h254, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                    · linarith only [h207, h248, h253, hlam]
                  · linarith only [h0, h247, h248, h252, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h0, h247, h248, h251, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h247, h248, h250, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h248, h249, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h270 | h270
            · linarith only [h248, h270, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
              · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                          · linarith only [h247, h248, h278, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                            · linarith only [h247, h248, h270, h272, h275, h280, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                              · linarith only [h273, h282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h277, h282, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h277, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h207, h248, h275, h276, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h287 | h287
                      · linarith only [h275, h287, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                          · linarith only [h247, h290, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                            · linarith only [h0, h247, h287, h292, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
                              · linarith only [h273, h294, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h289, h294, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h289, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h273, h274, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                  · linarith only [h273, h299, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
                    · linarith only [h272, h273, h301, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h303 | h303
                      · linarith only [h272, h273, h303, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                          · linarith only [h207, h301, h306, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                            · linarith only [h0, h207, h247, h273, h303, h306, h308, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                                · rcases h3bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h207, hlam, p312_1]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h0, h247, h299, h306, h310, hc23, hc34, hlam, hphi, p312_1]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h248, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h270, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h272, h299, h306, h310, hc03, hc34, hlam, hphi, p312_1]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h272, h299, h306, h310, hc23, hc34, hlam, hphi, p312_1]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h301, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h303, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h247, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h272, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h306, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h308, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    rcases p312_3 (m.d 0 3) (by simp) with h328 | h328
                                    · linarith only [h328, hlam, p312_0]
                                    · rcases p312_3 (m.d 1 3) (by simp) with h330 | h330
                                      · linarith only [h301, h330, hlam]
                                      · linarith only [h207, h330, hlam]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h207, hc01, hc34, hlam, hphi, ht12, ht23, p312_1]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    rcases p312_3 (m.d 0 3) (by simp) with h334 | h334
                                    · linarith only [h248, h334, hlam]
                                    · linarith only [h247, h334, hlam]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h0, h299, h308, hc02, hc34, hlam, hphi, ht23, p312_1]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    rcases p312_3 (m.d 0 3) (by simp) with h339 | h339
                                    · linarith only [h339, hlam, p312_0]
                                    · rcases p312_3 (m.d 1 3) (by simp) with h341 | h341
                                      · linarith only [h303, h341, hlam]
                                      · linarith only [h207, h341, hlam]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h207, hc01, hc35, hlam, hphi, ht12, ht23, p312_1]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    rcases p312_3 (m.d 0 3) (by simp) with h345 | h345
                                    · linarith only [h270, h345, hlam]
                                    · linarith only [h247, h345, hlam]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [h311, hlam, p312_0]
                                  · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                                    linarith only [hlam, p312_0]
                                · linarith only [h305, h306, h311, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h273, h305, h310, hlam]
                        · linarith only [h305, hc45, hlam, hphi, u4ehi1]
              · linarith only [h0, h247, h272, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h354 | h354
          · rcases m.htr 0 3 5 (by decide) (by decide) with h355 | h355
            · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
              · linarith only [h247, h354, h356, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                · linarith only [h356, h358, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                  · linarith only [h356, h360, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h366 | h366
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
                                · linarith only [h354, h368, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h364, h368, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h358, h364, h367, hlam]
                            · linarith only [h207, h355, h356, h366, hlam]
                          · linarith only [h207, h355, h356, h365, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h245, h364, hc45, hlam, hphi, u4ehi0]
                      · linarith only [h207, h354, h355, h363, hc05, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h207, h354, h362, hlam]
            · linarith only [h354, h355, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h378 | h378
            · linarith only [h354, h378, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
              · rcases m.htr 1 2 4 (by decide) (by decide) with h381 | h381
                · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                          · linarith only [h380, h386, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h247, h380, h383, h386, hc01, hc12, hlam, hphi]
                        · linarith only [h385, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h354, h383, h384, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                      · linarith only [h383, h391, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                          · linarith only [h354, h380, h394, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                            · linarith only [h378, h380, h396, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                              · linarith only [h381, h398, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h393, h398, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h393, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h0, h247, h380, h382, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h247, h380, h381, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                · linarith only [h380, h404, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                  · linarith only [h380, h406, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h412 | h412
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h413 | h413
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                                · linarith only [h408, h414, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h410, h414, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h404, h410, h413, hlam]
                            · linarith only [h380, h409, h412, hlam]
                          · linarith only [h378, h380, h409, h411, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · linarith only [h410, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h354, h408, h409, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                      · linarith only [h408, h422, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h424 | h424
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h425 | h425
                          · linarith only [h207, h408, h425, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h380, h425, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h424, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB3_H_R_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h3ehi := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · linarith only [h3, h4, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h2, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h8, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h15, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h15, hc45, hlam, hphi, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
        · linarith only [h0, h18, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
          · linarith only [h1, h18, h2, h20, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
            · linarith only [h1, h2, h20, h22, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h1, h2, h22, hc34, hlam, hphi, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
      · linarith only [h1, h25, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
        · linarith only [h0, h1, h27, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
          · linarith only [h0, h1, h27, h29, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
            · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
              · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h27, h31, h36, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h36, hc45, hlam, hphi, u4ehi3]
                    · linarith only [h29, h32, h35, hlam]
                  · linarith only [h0, h25, h27, h31, h34, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h27, h31, h32, h33, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h25, h32, hc45, hlam, hphi, u4ehi0]
            · linarith only [h0, h1, h31, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h44 | h44
    · rcases m.htr 0 1 4 (by decide) (by decide) with h45 | h45
      · linarith only [h0, h45, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
        · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
          · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
            · linarith only [h44, h45, h48, h49, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · linarith only [h44, h45, h49, hc34, hlam, hphi, u3ehi1]
          · linarith only [h0, h44, h47, h48, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
        · linarith only [h0, h44, h47, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h54 | h54
      · linarith only [h0, h54, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
        · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
          · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
            · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
              · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                · linarith only [h56, h60, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                  · linarith only [h60, h62, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h56, h58, h60, h64, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h64, hc45, hlam, hphi, u4ehi2]
              · linarith only [h59, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
              · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                · linarith only [h44, h58, h69, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                  · linarith only [h56, h71, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                    · linarith only [h57, h73, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h68, h73, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h68, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
            · linarith only [h56, h57, h77, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
              · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                · linarith only [h56, h57, h77, h80, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h56, h57, h80, hc34, hlam, hphi, u3ehi2]
              · linarith only [h79, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
          · linarith only [h56, h84, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
            · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
              · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                      · linarith only [h86, h91, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h87, h91, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h84, h87, h90, hlam]
                  · linarith only [h84, h87, h88, h89, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · linarith only [h56, h86, h87, h88, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h87, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
              · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                · linarith only [h44, h86, h99, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h56, h99, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h98, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB3_H_R_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h3elo := hb3.1
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi3]

theorem n7l_sAB3_H_R_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h3, h8, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h8, hc45, hlam, hphi, u4ehi2]
                · linarith only [h6, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h13, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h16, hc45, hlam, hphi, u4ehi2]
            · linarith only [h2, h5, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h21, h23, h25, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h21, h22, h25, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h23, h24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                  · linarith only [h21, h3, h30, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h22, h30, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h21, h23, h3, h33, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h3, h33, hc45, hlam, hphi, u4ehi1]
            · linarith only [h2, h22, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
            · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
              · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h38, h41, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h41, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h3, h37, h40, hlam]
                · linarith only [h3, h37, h38, h39, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h38, h46, h48, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h21, h37, h38, h46, h48, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h3, h37, h47, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                    · rcases h5bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h0, h37, hc01, hlam, hphi, ht0b, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h0, h21, h37, hc01, hlam, hphi, ht0b, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h0, h21, h37, h46, hc01, hlam, hphi, ht0b, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h0, hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h21, hlam, p54_1]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h21, h46, hlam, p54_1]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h1, hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h1, hc02, hlam, hphi, ht0b, ht5b, p54_1, u5ehi1]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h46, hlam, p54_1]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h0, h37, h53, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h37, h53, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h21, h53, hc12, hc34, hlam, hphi, ht23, p54_1]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h53, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p54_1, u4ehi4]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h2, hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h37, hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h52, hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [h53, hlam, p54_0]
                      · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                        linarith only [hlam, p54_0]
                    · linarith only [h37, h53, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h3, h37, h52, hlam]
            · linarith only [h37, hc45, hlam, hphi, u4ehi1]
      · linarith only [h2, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
      · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
        · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
          · linarith only [h0, h1, h86, hlam]
          · linarith only [h85, h86, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
          · linarith only [h1, h85, h89, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
            · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
              · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h95 | h95
                    · linarith only [h92, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h91, h95, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h91, h94, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h92, h93, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                    · linarith only [h100, h102, h92, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h100, h102, h89, h91, h92, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h101, h85, h91, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                    · rcases h5bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h91, hc05, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h1, hlam, p108_1]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h1, h100, hlam, p108_1]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h0, hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h89, hlam, p108_1]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p108_1, u5ehi3]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h106, h84, h92, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h106, h91, h92, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h100, hlam, p108_1]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h106, h92, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h0, h91, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h107, h91, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h1, h107, hc02, hc34, hlam, hphi, ht23, p108_1]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h84, hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h91, hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h106, hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [h107, hlam, p108_0]
                      · obtain ⟨p108_0, p108_1, p108_2, p108_3⟩ := h108c
                        linarith only [hlam, p108_0]
                    · linarith only [h107, h91, h92, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h106, h85, h91, hlam]
            · linarith only [h91, hc45, hlam, hphi, u4ehi1]
      · linarith only [h84, hc45, hlam, hphi, u4ehi0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h138 | h138
    · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
      · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
        · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
          · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
            · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
              · rcases m.htr 2 3 5 (by decide) (by decide) with h144 | h144
                · rcases m.htr 2 4 5 (by decide) (by decide) with h145 | h145
                  · linarith only [h140, h145, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h142, h145, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h143, h144, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                  · linarith only [h140, h150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h142, h150, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h140, h153, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h142, h153, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h142, hc45, hlam, hphi, u4ehi1]
          · linarith only [h138, h140, h141, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
          · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
            · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
              · rcases m.htr 2 3 5 (by decide) (by decide) with h161 | h161
                · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h140, h158, h160, h162, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h140, h158, h159, h162, hc01, hc14, hlam, hphi]
                · linarith only [h160, h161, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                  · linarith only [h140, h158, h167, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h139, h140, h158, h167, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
                  · linarith only [h140, h158, h160, h170, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h139, h140, h158, h170, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h139, h140, h158, h159, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h138, h158, hlam]
      · linarith only [h139, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h176 | h176
      · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
        · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
          · rcases m.htr 1 4 5 (by decide) (by decide) with h179 | h179
            · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
              · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                · rcases m.htr 2 4 5 (by decide) (by decide) with h182 | h182
                  · linarith only [h177, h182, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h179, h182, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h180, h181, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                  · linarith only [h177, h187, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h187, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h190 | h190
                  · linarith only [h177, h190, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h190, hc45, hlam, hphi, u4ehi2]
            · linarith only [h138, h176, h178, h179, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h177, h178, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
          · linarith only [h138, h177, h195, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
            · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
              · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h198, h201, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h201, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h177, h200, hc45, hlam, hphi, u4ehi1]
                · linarith only [h177, h197, h198, h199, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                    · linarith only [h198, h206, h208, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h197, h208, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h177, h197, h207, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h213 | h213
                    · rcases h5bigk with h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h0, hlam, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h138, hlam, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h0, h195, h206, hlam, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h176, h195, h206, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h195, hlam, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h177, h197, h198, h206, hc23, hc34, hlam, hphi, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h177, h197, h198, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h176, h198, h212, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h0, h198, h212, hc01, hc34, hlam, hphi, ht12, ht23, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h206, hlam, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h198, h212, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h176, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h0, h176, h213, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h138, h213, hc02, hc34, hlam, hphi, ht23, p214_1]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h213, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p214_1, u4ehi4]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h176, hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h197, hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h212, hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [h213, hlam, p214_0]
                      · obtain ⟨p214_0, p214_1, p214_2, p214_3⟩ := h214c
                        linarith only [hlam, p214_0]
                    · linarith only [h177, h198, h213, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h177, h212, hc45, hlam, hphi, u4ehi1]
            · linarith only [h197, hc45, hlam, hphi, u4ehi1]
      · linarith only [h176, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB3_H_R_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · linarith only [h0, h4, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · linarith only [h1, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
          · rcases h5emax with h10 | h10 | h10 | h10 | h10
            · linarith only [h0, h10, hlam, ht45, u4ehi4]
            · linarith only [h1, h10, hlam, ht45, u4ehi4]
            · linarith only [h10, h8, hlam, ht45, u4ehi4]
            · linarith only [h10, h9, hlam, ht45, u4ehi4]
            · linarith only [h10, hlam, ht45, u4ehi4]
          · linarith only [h2, h9, hc45, hlam, hphi, u4ehi2]
        · linarith only [h1, h8, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · linarith only [h1, hc45, hlam, hphi, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB3_M_IR_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5emax := hb5.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases h5emax with h0 | h0 | h0 | h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, ht45, u4ehi4]
    · linarith only [h0, h1, hlam, ht45, u4ehi0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
      · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
        · linarith only [h0, h6, hlam, ht45, u4ehi4]
        · linarith only [h0, h5, h6, hlam, ht45, u4ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
        · linarith only [h0, h9, hlam, ht45, u4ehi4]
        · linarith only [h0, h9, hlam, ht45, u4ehi1]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
      · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
        · linarith only [h0, h13, h4, hlam, ht45, u4ehi0]
        · linarith only [h0, h12, h13, hlam, ht45, u4ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
        · linarith only [h0, h16, hlam, ht45, u4ehi4]
        · linarith only [h0, h16, hlam, ht45, u4ehi1]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
    · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
      · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
        · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
          · linarith only [h0, h22, hlam, ht45, u4ehi4]
          · linarith only [h0, h22, hlam, ht45, u4ehi2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
          · linarith only [h20, h21, h25, hlam]
          · linarith only [h0, h25, hlam, ht45, u4ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
          · linarith only [h0, h29, hlam, ht45, u4ehi4]
          · linarith only [h20, h28, h29, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
          · linarith only [h0, h28, h32, hlam, ht45, u4ehi1]
          · linarith only [h0, h20, h32, hc12, hlam, ht23, ht34, ht45]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
      · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
        · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
          · linarith only [h19, h35, h37, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
          · linarith only [h0, h37, hlam, ht45, u4ehi2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
          · linarith only [h35, h36, h40, hlam]
          · linarith only [h0, h40, hlam, ht45, u4ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
        · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
          · linarith only [h0, h44, hlam, ht45, u4ehi4]
          · linarith only [h35, h43, h44, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
          · linarith only [h0, h35, h43, h47, hc12, hlam, ht23, ht34, ht45]
          · linarith only [h0, h35, h47, hc12, hlam, ht23, ht34, ht45]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
    · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
      · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
        · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
          · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
            · linarith only [h0, h54, hlam, ht45, u4ehi4]
            · linarith only [h51, h53, h54, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
            · linarith only [h0, h53, h57, hlam, ht45, u4ehi2]
            · linarith only [h0, h57, hlam, ht45, u4ehi3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
          · linarith only [h51, h52, h60, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h51, h52, h62, hlam, ht45, u4ehi2]
            · linarith only [h0, h62, hlam, ht45, u4ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
        · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
          · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
            · linarith only [h0, h67, hlam, ht45, u4ehi4]
            · linarith only [h0, h67, hlam, ht45, u4ehi3]
          · linarith only [h51, h65, h66, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
          · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
            · linarith only [h0, h65, h72, hlam, ht45, u4ehi1]
            · linarith only [h0, h72, hlam, ht45, u4ehi3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
            · linarith only [h51, h71, h75, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h75, hlam, ht45, u4ehi3]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
      · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
        · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
          · linarith only [h50, h78, h80, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
            · linarith only [h0, h50, h82, hlam, ht45, u4ehi0]
            · linarith only [h0, h82, hlam, ht45, u4ehi3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
          · linarith only [h78, h79, h85, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
            · linarith only [h0, h78, h79, h87, hlam, ht45, u4ehi2]
            · linarith only [h0, h87, hlam, ht45, u4ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
        · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
          · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
            · linarith only [h0, h92, hlam, ht45, u4ehi4]
            · linarith only [h0, h92, hlam, ht45, u4ehi3]
          · linarith only [h78, h90, h91, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
          · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
            · linarith only [h0, h90, h97, hlam, ht45, u4ehi1]
            · linarith only [h0, h97, hlam, ht45, u4ehi3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
            · linarith only [h100, h78, h96, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h100, hlam, ht45, u4ehi3]
  · linarith only [h0, hlam, ht45, u4ehi4]

theorem n7l_sAB3_M_IR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
        · linarith only [h2, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
          · linarith only [h2, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
              · linarith only [h11, h2, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                · linarith only [h11, h13, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h1, h11, h15, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h11, h17, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h19, h6, hc03, hlam, hphi, u3elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h1, h15, h21, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                          · linarith only [h23, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                          · rcases h4bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h10, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p25_1, u3elo3, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h2, h23, hc45, hlam, hphi, p25_1, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h2, hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h8, hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h11, h23, hc45, hlam, hphi, p25_1, u4ehi0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h11, h23, hc45, hlam, hphi, p25_1, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h11, hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h15, hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h1, hlam, p25_1]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h10, hlam, p25_1]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h17, hlam, p25_1]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h21, hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h1, h23, hc45, hlam, hphi, p25_1, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h23, hc45, hlam, hphi, p25_1, u4ehi1]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h23, hc45, hlam, hphi, p25_1, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h23, hlam, p25_0]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h1, hc45, hlam, hphi, p25_1, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [h10, hc45, hlam, hphi, p25_1, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [hc45, hlam, hphi, p25_1, u4ehi2]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [hc45, hlam, hphi, p25_1, u4ehi3]
                            · obtain ⟨p25_0, p25_1, p25_2, p25_3⟩ := h25c
                              linarith only [hlam, p25_0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
              · linarith only [h1, h10, h2, h51, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                · linarith only [h51, h53, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h1, h10, h55, h8, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h51, h57, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h59, h6, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                        · linarith only [h1, h61, h8, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                          · linarith only [h1, h10, h63, h8, hc12, hlam, hphi, ht23, u3elo3]
                          · rcases h4bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h2, h63, hc45, hlam, hphi, p65_1, u4ehi1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h10, h2, h63, hc12, hc45, hlam, hphi, ht23, ht34, p65_1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h2, hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h8, hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h1, h10, hc02, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h10, hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h51, hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h55, hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h1, hlam, p65_1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p65_1, u4ehi1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h57, hlam, p65_1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h61, hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h63, hc45, hlam, hphi, p65_1, u4ehi0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h63, hc45, hlam, hphi, p65_1, u4ehi1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h10, h63, hc12, hc45, hlam, hphi, ht23, ht34, p65_1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h63, hlam, p65_0]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h1, h10, hc12, hc45, hlam, hphi, ht23, ht34, p65_1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [hc45, hlam, hphi, p65_1, u4ehi1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h10, hc12, hc45, hlam, hphi, ht23, ht34, p65_1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [h2, hc03, hc45, hlam, hphi, ht34, p65_1]
                            · obtain ⟨p65_0, p65_1, p65_2, p65_3⟩ := h65c
                              linarith only [hlam, p65_0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
      · linarith only [h0, h1, h91, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h93 | h93
        · linarith only [h91, h93, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h95 | h95
          · linarith only [h91, h95, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
            · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
              · linarith only [h91, h98, hc03, hlam, hphi, u3elo1]
              · linarith only [h0, h1, h97, h98, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
              · linarith only [h0, h101, h91, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                · linarith only [h101, h103, h93, h95, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h1, h101, h105, h95, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                    · linarith only [h0, h1, h101, h107, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h107, hc23, hlam, hphi, u3elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h110 | h110
    · linarith only [h0, h110, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h112 | h112
      · rcases m.htr 0 3 5 (by decide) (by decide) with h113 | h113
        · linarith only [h113, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
        · linarith only [h112, h113, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
        · linarith only [h112, h116, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
          · linarith only [h112, h118, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
              · linarith only [h112, h121, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h123 | h123
                · linarith only [h116, h121, h123, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                  · linarith only [h118, h121, h125, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                    · linarith only [h121, h127, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h127, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
              · linarith only [h0, h112, h130, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                · linarith only [h130, h132, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
                  · linarith only [h118, h130, h134, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                    · linarith only [h130, h136, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h136, hc02, hlam, hphi, ht23, u3elo3]

theorem n7l_sAB3_M_IR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_IR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
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
            · linarith only [h38, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc45, hlam, hphi, ht34, p0_1, u3ehi3]
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
            · linarith only [h116, hc45, hlam, hphi, ht34, p0_1, u3ehi3]
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
            · linarith only [h189, hc45, hlam, hphi, ht34, p0_1, u3ehi3]
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
            · linarith only [h284, h295, hc45, hlam, hphi, p0_1, u4ehi1]
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

theorem n7l_sAB3_M_IR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht45, u4ehi3, u5elo0]
      · linarith only [h1, h2, hlam, hphi, ht45, u4ehi2, u5elo1]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB3_M_IR_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht45, u4ehi3, u5elo0]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi2, u5elo0]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB3_M_IR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h3ehi := hb3.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB3_M_IR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3elo := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h10, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h10, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h0, h2, h6, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi2]
                  · linarith only [h7, h8, hlam, hphi, ht45, u4ehi3, u5elo3]
                · linarith only [h2, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h6, hlam, hphi, ht45, u4ehi1, u5elo4]
            · linarith only [h2, h5, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h2, h23, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h23, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h19, h22, h4, hlam]
                  · linarith only [h20, h21, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                · linarith only [h2, h20, hc23, hlam, hphi, u3elo0]
              · linarith only [h19, hlam, hphi, ht45, u4ehi1, u5elo4]
            · linarith only [h18, h2, hc13, hlam, hphi, u3elo0]
        · linarith only [h3, hlam, hphi, ht45, u4ehi0, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
        · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
          · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
            · linarith only [h2, h32, h34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
              · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                · linarith only [h0, h2, h36, h37, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h37, h39, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                      · rcases h4bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi1]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi2]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h2, hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi4]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h0, hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p43_1, u4ehi2]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h34, hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi4]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h1, hlam, p43_1]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h33, hlam, p43_1]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h37, hlam, p43_1]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p43_1, u4ehi4]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi1]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi2]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p43_1, u3elo3, u4ehi4]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h32, hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h36, hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h41, hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [h42, hlam, p43_0]
                        · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                          linarith only [hlam, p43_0]
                      · linarith only [h2, h33, h41, h42, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h2, h36, h41, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · linarith only [h36, hlam, hphi, ht45, u4ehi1, u5elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
            · linarith only [h2, h32, h72, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                · linarith only [h1, h2, h33, h74, h75, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h75, h77, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                      · rcases h4bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h74, hc04, hlam, hphi, ht0b, ht45, ht5b, p81_1, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h0, h33, h74, hc01, hlam, hphi, ht0b, ht45, ht5b, p81_1, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h2, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p81_1, u3elo3, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h0, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h33, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h72, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p81_1, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h1, hlam, p81_1]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p81_1, u4ehi1]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h75, hlam, p81_1]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p81_1, u3elo3, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p81_1, u3elo3, u4ehi0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h74, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p81_1, u3elo3, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h33, h74, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p81_1, u3elo3, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p81_1, u3elo3, u4ehi4]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h32, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h74, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h79, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [h80, hlam, p81_0]
                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                          linarith only [hlam, p81_0]
                      · linarith only [h72, h80, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h33, h74, h79, hlam]
              · linarith only [h74, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h32, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h111 | h111
      · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
        · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
          · linarith only [h0, h1, h113, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
            · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
              · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h111, h120, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h120, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h0, h1, h116, h119, hlam]
                  · linarith only [h113, h117, h118, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h111, h117, hc23, hlam, hphi, u3elo0]
              · linarith only [h116, hlam, hphi, ht45, u4ehi1, u5elo4]
            · linarith only [h111, h115, hc13, hlam, hphi, u3elo0]
        · linarith only [h112, hlam, hphi, ht45, u4ehi0, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h129 | h129
        · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
          · linarith only [h0, h1, h130, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
            · linarith only [h111, h132, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
              · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                · linarith only [h0, h111, h134, h135, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                  · linarith only [h135, h137, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                      · rcases h4bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h134, hc04, hlam, hphi, ht0b, ht45, ht5b, p141_1, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h1, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h111, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h111, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u3elo3, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h0, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h130, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h132, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p141_1, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h129, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p141_1, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h134, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p141_1, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h135, hlam, p141_1]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h135, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u3elo3, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h0, h134, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u3elo3, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h134, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u3elo3, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h130, hc12, hlam, hphi, ht23, p141_1, u3elo3]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p141_1, u3elo3, u4ehi4]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h129, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h134, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h139, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [h140, hlam, p141_0]
                        · obtain ⟨p141_0, p141_1, p141_2, p141_3⟩ := h141c
                          linarith only [hlam, p141_0]
                      · linarith only [h132, h140, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h1, h134, h139, hlam]
              · linarith only [h134, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h129, hlam, hphi, ht45, u4ehi0, u5elo4]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h171 | h171
    · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
      · rcases m.htr 0 4 5 (by decide) (by decide) with h173 | h173
        · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
          · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
            · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
              · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                      · linarith only [h172, h180, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h171, h179, h180, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h173, h175, h179, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi2]
                  · linarith only [h177, h178, hlam, hphi, ht45, u4ehi3, u5elo3]
                · linarith only [h172, h177, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h173, h176, hlam]
            · linarith only [h172, h175, hc13, hlam, hphi, u3elo0]
          · linarith only [h0, h171, h174, hlam]
        · linarith only [h173, hlam, hphi, ht45, u4ehi0, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
        · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
          · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
            · linarith only [h172, h192, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
              · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                · linarith only [h0, h190, h192, h195, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h195, h197, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                      · rcases h4bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h0, hlam, p201_1]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h172, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi2]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h172, hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h172, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi4]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h190, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p201_1, u4ehi4]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h192, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi2]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h192, hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h192, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi4]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h171, hlam, p201_1]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h191, hlam, p201_1]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h195, hlam, p201_1]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h171, hc02, hlam, hphi, ht0b, ht45, ht5b, p201_1, u4ehi4]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi1]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi2]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p201_1, u3elo3, u4ehi4]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h190, hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h194, hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h199, hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [h200, hlam, p201_0]
                        · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                          linarith only [hlam, p201_0]
                      · linarith only [h192, h200, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h190, h192, h199, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · linarith only [h0, h190, h194, hlam]
          · linarith only [h0, h171, h191, hlam]
        · linarith only [h190, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h232 | h232
      · rcases m.htr 0 4 5 (by decide) (by decide) with h233 | h233
        · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
          · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
            · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
              · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                      · linarith only [h232, h240, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h171, h233, h234, h240, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h171, h233, h239, hlam]
                  · linarith only [h171, h233, h237, h238, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi9]
                · linarith only [h232, h237, hc23, hlam, hphi, u3elo0]
              · linarith only [h236, hlam, hphi, ht45, u4ehi1, u5elo4]
            · linarith only [h232, h235, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
            · rcases m.htr 1 4 5 (by decide) (by decide) with h249 | h249
              · rcases m.htr 2 3 4 (by decide) (by decide) with h250 | h250
                · rcases m.htr 2 3 5 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h253 | h253
                      · linarith only [h232, h253, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi9]
                      · linarith only [h253, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h0, h233, h234, h252, hlam]
                  · linarith only [h234, h250, h251, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h232, h250, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h233, h249, hlam]
            · linarith only [h232, h248, hc13, hlam, hphi, u3elo0]
        · linarith only [h233, hlam, hphi, ht45, u4ehi0, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
          · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
            · linarith only [h232, h264, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
              · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                · linarith only [h264, h267, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                  · linarith only [h267, h269, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h272 | h272
                      · rcases h4bigk with h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h0, hlam, p273_1]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h171, hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h232, hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h171, h263, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p273_1, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h262, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p273_1, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h171, h262, h263, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p273_1, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h264, hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h264, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p273_1, u3elo3, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h262, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p273_1, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h263, hlam, p273_1]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h267, hlam, p273_1]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h263, h264, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p273_1, u3elo3, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h262, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p273_1, u3elo3, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h171, h263, hc02, hlam, hphi, ht23, p273_1, u3elo3]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h171, h262, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p273_1, u3elo3, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p273_1, u3elo3, u4ehi4]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h262, hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h266, hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h271, hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [h272, hlam, p273_0]
                        · obtain ⟨p273_0, p273_1, p273_2, p273_3⟩ := h273c
                          linarith only [hlam, p273_0]
                      · linarith only [h272, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h171, h262, h271, hlam]
              · linarith only [h171, h262, h263, h266, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
            · linarith only [h232, h302, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h304 | h304
              · rcases m.htr 2 3 4 (by decide) (by decide) with h305 | h305
                · linarith only [h0, h262, h302, h305, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                  · linarith only [h305, h307, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                      · rcases h4bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h0, hlam, p311_1]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h171, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h232, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h232, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p311_1, u3elo3, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h262, h263, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p311_1, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h263, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h302, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h302, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p311_1, u3elo3, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h262, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p311_1, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p311_1]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h305, hlam, p311_1]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h305, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p311_1, u3elo3, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h262, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p311_1, u3elo3, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h0, h262, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p311_1, u3elo3, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h263, hc12, hlam, hphi, ht23, p311_1, u3elo3]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p311_1, u3elo3, u4ehi4]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h262, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h304, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h309, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [h310, hlam, p311_0]
                        · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                          linarith only [hlam, p311_0]
                      · linarith only [h302, h310, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h262, h263, h309, hlam]
              · linarith only [h0, h262, h304, hlam]
        · linarith only [h262, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB3_M_IR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3ehi := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h11, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h11, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h10, h4, hlam, hphi, ht45, u4ehi2, u5elo0]
                    · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h8, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h16, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h4, h7, hlam, hphi, ht45, u4ehi1, u5elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h23, h5, h6, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h23, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h20, hlam, hphi, ht45, u4ehi1, u5elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                        · rcases h4bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h0, h27, h32, hc01, hlam, hphi, ht0b, ht5b, p33_1, u5ehi9]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h0, h29, h32, hc01, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h0, h32, hc01, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            rcases p33_3 (m.d 0 4) (by simp) with h38 | h38
                            · rcases p33_3 (m.d 1 4) (by simp) with h39 | h39
                              · linarith only [h0, h39, hlam]
                              · linarith only [h28, h39, hlam]
                            · linarith only [h38, hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h0, hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h29, h32, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h0, h32, hc01, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h1, hlam, p33_1]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi1]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h32, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h2, hlam, p33_1]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h27, hlam, p33_1]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h29, hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h0, h27, hc01, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi4]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h4, hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h28, hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h31, hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [h32, hlam, p33_0]
                          · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                            linarith only [hlam, p33_0]
                        · linarith only [h32, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h31, h4, hlam, hphi, ht45, u4ehi2, u5elo0]
                    · linarith only [h3, h30, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                  · linarith only [h27, h29, h5, hlam]
                · linarith only [h28, hlam, hphi, ht45, u4ehi1, u5elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                        · rcases h4bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h0, h68, hc01, hlam, hphi, ht0b, ht5b, p73_1, u5ehi9]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h0, h27, h69, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1, u3ehi1]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h0, h27, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p73_1, u3ehi1]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            rcases p73_3 (m.d 0 4) (by simp) with h78 | h78
                            · rcases p73_3 (m.d 1 4) (by simp) with h79 | h79
                              · linarith only [h0, h79, hlam]
                              · linarith only [h68, h79, hlam]
                            · linarith only [h78, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h0, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h27, h69, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p73_1, u3ehi1]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h27, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h1, hlam, p73_1]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi1]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi3]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h2, hlam, p73_1]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h68, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p73_1, u4ehi4]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h69, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h69, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u4ehi4]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h4, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h68, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h71, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [h72, hlam, p73_0]
                          · obtain ⟨p73_0, p73_1, p73_2, p73_3⟩ := h73c
                            linarith only [hlam, p73_0]
                        · linarith only [h72, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h71, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h27, h3, h69, h70, hlam, hphi, ht45, u4ehi1, u5elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                    · linarith only [h106, h69, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h106, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h68, hlam, hphi, ht45, u4ehi1, u5elo4]
          · linarith only [h4, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h3, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
        · linarith only [h112, h2, hc34, hlam, hphi, u3ehi4]
        · linarith only [h112, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h115 | h115
      · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
        · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
          · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
            · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
              · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                        · linarith only [h118, h121, h124, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h124, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h0, h1, h120, h123, hlam]
                    · linarith only [h1, h121, h122, hlam, hphi, ht45, u4ehi0, u5elo3]
                  · linarith only [h0, h1, h119, h121, hlam]
                · linarith only [h120, hlam, hphi, ht45, u4ehi1, u5elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                  · linarith only [h118, h119, h132, hlam]
                  · linarith only [h1, h115, h132, hlam]
                · linarith only [h131, hlam, hphi, ht45, u4ehi1, u5elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
              · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                        · rcases h4bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h1, h136, h138, h141, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h1, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h1, h138, h141, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            rcases p142_3 (m.d 0 4) (by simp) with h147 | h147
                            · rcases p142_3 (m.d 1 4) (by simp) with h148 | h148
                              · linarith only [h0, h148, hlam]
                              · linarith only [h137, h148, hlam]
                            · linarith only [h147, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h0, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h0, h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p142_1, u4ehi0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h0, h141, hc01, hlam, hphi, ht0b, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h115, h141, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h136, h138, h141, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h138, h141, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            rcases p142_3 (m.d 0 4) (by simp) with h161 | h161
                            · linarith only [h1, h161, hlam]
                            · linarith only [h117, h161, hlam]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h115, hlam, p142_1]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h136, hlam, p142_1]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h138, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h136, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1, u4ehi4]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h117, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h137, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h140, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [h141, hlam, p142_0]
                          · obtain ⟨p142_0, p142_1, p142_2, p142_3⟩ := h142c
                            linarith only [hlam, p142_0]
                        · linarith only [h141, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h140, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h116, h118, h139, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                  · linarith only [h118, h136, h138, hlam]
                · linarith only [h137, hlam, hphi, ht45, u4ehi1, u5elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h179 | h179
                · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h182 | h182
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                        · rcases h4bigk with h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h1, h179, h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p184_1, u4ehi4]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h1, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h1, h136, h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p184_1, u3ehi1]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            rcases p184_3 (m.d 0 4) (by simp) with h189 | h189
                            · rcases p184_3 (m.d 1 4) (by simp) with h190 | h190
                              · linarith only [h0, h190, hlam]
                              · linarith only [h179, h190, hlam]
                            · linarith only [h189, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h0, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h0, h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p184_1, u4ehi0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h136, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h115, h136, hc03, hlam, hphi, ht0b, ht45, ht5b, p184_1, u4ehi4]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h117, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p184_1, u4ehi4]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h179, h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p184_1, u4ehi4]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h136, h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p184_1, u3ehi1]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            rcases p184_3 (m.d 0 4) (by simp) with h203 | h203
                            · linarith only [h1, h203, hlam]
                            · linarith only [h117, h203, hlam]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h115, hlam, p184_1]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h115, h179, hc04, hlam, hphi, ht0b, ht45, ht5b, p184_1, u4ehi4]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h180, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p184_1, u4ehi4]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h117, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h179, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h182, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [h183, hlam, p184_0]
                          · obtain ⟨p184_0, p184_1, p184_2, p184_3⟩ := h184c
                            linarith only [hlam, p184_0]
                        · linarith only [h183, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h1, h136, h179, h180, h182, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h116, h136, h180, h181, hlam, hphi, ht45, u4ehi1, u5elo0]
                  · linarith only [h1, h115, h180, hlam]
                · linarith only [h179, hlam, hphi, ht45, u4ehi1, u5elo4]
          · linarith only [h117, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h116, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h223 | h223
        · linarith only [h115, h223, hc34, hlam, hphi, u3ehi4]
        · linarith only [h223, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h226 | h226
    · rcases m.htr 0 3 4 (by decide) (by decide) with h227 | h227
      · rcases m.htr 0 3 5 (by decide) (by decide) with h228 | h228
        · rcases m.htr 0 4 5 (by decide) (by decide) with h229 | h229
          · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
            · rcases m.htr 1 3 4 (by decide) (by decide) with h231 | h231
              · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h235 | h235
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
                        · linarith only [h230, h233, h236, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h226, h235, h236, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h235, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h234, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h233, h241, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h241, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · linarith only [h0, h229, h232, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h0, h227, h231, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
              · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
                        · rcases h4bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h0, hlam, p252_1]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h0, h230, h246, h250, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h0, h230, h246, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            rcases p252_3 (m.d 0 4) (by simp) with h257 | h257
                            · rcases p252_3 (m.d 1 4) (by simp) with h258 | h258
                              · rcases p252_3 (m.d 2 4) (by simp) with h259 | h259
                                · linarith only [h226, h259, hlam]
                                · linarith only [h250, h259, hlam]
                              · linarith only [h247, h258, hlam]
                            · linarith only [h257, hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h226, h230, h246, h248, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h230, h246, h248, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h230, h246, h251, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            rcases p252_3 (m.d 0 4) (by simp) with h268 | h268
                            · linarith only [h0, h268, hlam]
                            · linarith only [h229, h268, hlam]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h226, hlam, p252_1]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p252_1]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h226, h251, hc02, hlam, hphi, ht0b, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h226, hc02, hlam, hphi, ht0b, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h227, hlam, p252_1]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h246, hlam, p252_1]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h248, hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h227, hc03, hlam, hphi, ht0b, ht45, ht5b, p252_1, u4ehi4]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h229, hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h247, hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h250, hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [h251, hlam, p252_0]
                          · obtain ⟨p252_0, p252_1, p252_2, p252_3⟩ := h252c
                            linarith only [hlam, p252_0]
                        · linarith only [h251, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h229, h250, hlam, hphi, ht45, u4ehi2, u5elo0]
                    · linarith only [h0, h228, h230, h246, h249, hlam, hphi, ht45, u4ehi0, u5elo0]
                  · linarith only [h0, h227, h229, h230, h246, h248, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h0, h229, h247, hlam]
              · linarith only [h0, h227, h246, hlam]
          · linarith only [h229, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h228, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h294 | h294
        · linarith only [h227, h294, hc34, hlam, hphi, u3ehi4]
        · linarith only [h294, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
      · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
        · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
          · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
            · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
              · rcases m.htr 1 4 5 (by decide) (by decide) with h302 | h302
                · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                        · linarith only [h300, h303, h306, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h306, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h226, h299, h305, hlam]
                    · linarith only [h226, h303, h304, hlam, hphi, ht45, u4ehi0, u5elo3]
                  · linarith only [h226, h297, h303, hlam]
                · linarith only [h0, h302, hlam, hphi, ht45, u4ehi0, u5elo4]
              · linarith only [h0, h297, h301, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h314 | h314
              · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h318 | h318
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h319 | h319
                        · rcases h4bigk with h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h0, hlam, p320_1]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h226, hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h319, hc04, hlam, hphi, ht0b, ht45, ht5b, p320_1, u4ehi4]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            rcases p320_3 (m.d 0 4) (by simp) with h325 | h325
                            · rcases p320_3 (m.d 1 4) (by simp) with h326 | h326
                              · rcases p320_3 (m.d 2 4) (by simp) with h327 | h327
                                · rcases p320_3 (m.d 3 4) (by simp) with h328 | h328
                                  · linarith only [h297, h328, hlam]
                                  · linarith only [h319, h328, hlam]
                                · linarith only [h318, h327, hlam]
                              · linarith only [h315, h326, hlam]
                            · linarith only [h325, hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h297, h300, h314, h319, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p320_1, u4ehi4]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h226, h297, h300, h314, h319, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p320_1, u4ehi4]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h300, h314, h319, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p320_1, u4ehi4]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            rcases p320_3 (m.d 0 4) (by simp) with h338 | h338
                            · linarith only [h0, h338, hlam]
                            · linarith only [h299, h338, hlam]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h297, h319, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p320_1, u4ehi4]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h0, h316, hc01, hc23, hlam, hphi, ht12, p320_1]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h316, h319, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p320_1, u4ehi4]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            rcases p320_3 (m.d 0 4) (by simp) with h345 | h345
                            · linarith only [h226, h345, hlam]
                            · linarith only [h299, h345, hlam]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h297, hlam, p320_1]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h314, hlam, p320_1]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h316, hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h297, hc03, hlam, hphi, ht0b, ht45, ht5b, p320_1, u4ehi4]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h299, hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h315, hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h318, hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [h319, hlam, p320_0]
                          · obtain ⟨p320_0, p320_1, p320_2, p320_3⟩ := h320c
                            linarith only [hlam, p320_0]
                        · linarith only [h319, hlam, hphi, ht45, u4ehi3, u5elo4]
                      · linarith only [h318, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h298, h300, h317, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
                  · linarith only [h0, h297, h299, h300, h314, h316, hc03, hlam, hphi, ht0b, ht5b, u5ehi9]
                · linarith only [h0, h299, h315, hlam]
              · linarith only [h0, h297, h314, hlam]
          · linarith only [h299, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h298, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h366 | h366
        · linarith only [h297, h366, hc34, hlam, hphi, u3ehi4]
        · linarith only [h366, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem n7l_sAB3_M_LI_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3elo := hb3.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
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
                · linarith only [h11, h12, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · rcases m.htr 0 1 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, h6, hlam]
                  · linarith only [h17, h18, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h6, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
                    · linarith only [h23, h8, hlam]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                            · linarith only [h17, h23, h28, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h17, h28, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h11, h27, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                        · linarith only [h11, h26, hc01, hlam, hphi, ht12, ht23, u3elo2]
                      · linarith only [h25, hlam, p0_0]
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
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · rcases p0_3 (m.d 4 5) (by simp) with h46 | h46
            · linarith only [h46, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
              · rcases m.htr 0 1 3 (by decide) (by decide) with h49 | h49
                · rcases m.htr 0 1 4 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h45, h51, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                          · linarith only [h44, h55, hlam]
                          · linarith only [h54, h55, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                          · linarith only [h44, h58, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                            · linarith only [h45, h60, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h63 | h63
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                                  · linarith only [h51, h64, hc03, hlam, hphi, u3elo2]
                                  · linarith only [h54, h64, hc12, hlam, hphi, ht23, u3elo3]
                                · linarith only [h63, hlam, p0_0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                                  · linarith only [h60, h69, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo2]
                                  · linarith only [h54, h69, hc12, hlam, hphi, ht23, u3elo3]
                                · linarith only [h68, hlam, p0_0]
                      · linarith only [h50, h53, hlam, p0_1]
                  · linarith only [h42, h50, hlam]
                · linarith only [h48, h49, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h48, h77, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h42, h77, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
                  · linarith only [h76, h80, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
                  · linarith only [h42, h80, hlam]
          · linarith only [h45, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h44, hc24, hlam, hphi, p0_1, u4elo1]
      · linarith only [h43, hlam, p0_0]
    · linarith only [h42, hc04, hlam, hphi, p0_1, u4elo1]
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
              · rcases m.htr 0 1 3 (by decide) (by decide) with h98 | h98
                · rcases m.htr 0 1 4 (by decide) (by decide) with h99 | h99
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
                    · linarith only [h100, h94, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                          · linarith only [h104, h97, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                          · linarith only [h104, h92, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                          · linarith only [h100, h103, h107, h98, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3]
                          · linarith only [h107, h92, hlam]
                      · linarith only [h102, h99, hc14, hlam, hphi, p0_1, u4elo2]
                  · linarith only [h97, h99, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · linarith only [h97, h98, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · linarith only [h114, h92, h97, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h113, h114, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h117 | h117
                  · linarith only [h113, h117, h92, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h119 | h119
                    · linarith only [h113, h119, h94, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                            · linarith only [h113, h119, h124, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h113, h124, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h123, h92, hlam]
                        · linarith only [h122, h97, hc01, hlam, hphi, ht12, ht23, u3elo2]
                      · linarith only [h121, h91, hlam, p0_1]
          · linarith only [h91, h94, hc34, hlam, hphi, p0_1, u4elo0]
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
    rcases p0_3 (m.d 0 4) (by simp) with h138 | h138
    · rcases p0_3 (m.d 1 4) (by simp) with h139 | h139
      · rcases p0_3 (m.d 2 4) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h144 | h144
              · rcases m.htr 0 1 3 (by decide) (by decide) with h145 | h145
                · rcases m.htr 0 1 4 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h147 | h147
                    · linarith only [h147, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                    · linarith only [h138, h147, hlam]
                  · linarith only [h145, h146, hc13, hlam, hphi, ht34, u4elo1]
                · linarith only [h144, h145, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h152 | h152
                · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
                  · linarith only [h139, h144, h153, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h152, h153, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h156 | h156
                  · linarith only [h139, h152, h156, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
                    · linarith only [h152, h158, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
                    · linarith only [h138, h158, hlam]
          · linarith only [h141, hlam, p0_0]
        · linarith only [h140, hc24, hlam, hphi, p0_1, u4elo3]
      · linarith only [h139, hc14, hlam, hphi, p0_1, u4elo3]
    · linarith only [h138, hc04, hlam, hphi, p0_1, u4elo3]
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

theorem n7l_sAB3_M_LI_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h3elo := hb3.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
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
                · linarith only [h11, h12, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                · rcases m.htr 0 1 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, h6, hlam]
                  · linarith only [h17, h18, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h6, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
                    · linarith only [h23, h8, hlam]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                            · linarith only [h17, h23, h28, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h17, h28, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h11, h27, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                        · linarith only [h11, h26, hc01, hlam, hphi, ht12, ht23, u3elo2]
                      · linarith only [h25, hlam, p0_0]
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
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · rcases p0_3 (m.d 4 5) (by simp) with h46 | h46
            · linarith only [h46, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
              · rcases m.htr 0 1 3 (by decide) (by decide) with h49 | h49
                · rcases m.htr 0 1 4 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h45, h51, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                          · linarith only [h44, h55, hlam]
                          · linarith only [h54, h55, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                          · linarith only [h44, h58, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                            · linarith only [h45, h60, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                              · linarith only [h51, h62, hc03, hlam, hphi, u3elo2]
                              · linarith only [h54, h62, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h50, h53, hlam, p0_1]
                  · linarith only [h42, h50, hlam]
                · linarith only [h48, h49, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
                  · linarith only [h48, h69, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h42, h69, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h72 | h72
                  · linarith only [h68, h72, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
                  · linarith only [h42, h72, hlam]
          · linarith only [h45, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h44, hc24, hlam, hphi, p0_1, u4elo1]
      · linarith only [h43, hlam, p0_0]
    · linarith only [h42, hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 4) (by simp) with h84 | h84
      · rcases p0_3 (m.d 2 4) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 4) (by simp) with h86 | h86
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h87, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 1 3 (by decide) (by decide) with h90 | h90
                · rcases m.htr 0 1 4 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h92 | h92
                    · linarith only [h86, h92, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                          · linarith only [h89, h96, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                          · linarith only [h84, h96, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                          · linarith only [h90, h92, h95, h99, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3]
                          · linarith only [h84, h99, hlam]
                      · linarith only [h91, h94, hc14, hlam, hphi, p0_1, u4elo2]
                  · linarith only [h89, h91, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · linarith only [h89, h90, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h105 | h105
                · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
                  · linarith only [h106, h84, h89, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h105, h106, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h109 | h109
                  · linarith only [h109, h84, h89, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h111 | h111
                    · linarith only [h105, h111, h86, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                            · linarith only [h105, h111, h116, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h105, h116, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h115, h84, hlam]
                        · linarith only [h114, h89, hc01, hlam, hphi, ht12, ht23, u3elo2]
                      · linarith only [h113, h83, hlam, p0_1]
          · linarith only [h83, h86, hc34, hlam, hphi, p0_1, u4elo0]
        · linarith only [h85, hlam, p0_0]
      · linarith only [h83, h84, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h83, hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h130 | h130
    · rcases p0_3 (m.d 1 4) (by simp) with h131 | h131
      · rcases p0_3 (m.d 2 4) (by simp) with h132 | h132
        · rcases p0_3 (m.d 3 4) (by simp) with h133 | h133
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h134, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 1 3 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 1 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h139 | h139
                    · linarith only [h139, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                    · linarith only [h130, h139, hlam]
                  · linarith only [h136, h138, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · linarith only [h136, h137, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h144 | h144
                · rcases m.htr 0 1 4 (by decide) (by decide) with h145 | h145
                  · linarith only [h131, h136, h145, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · linarith only [h144, h145, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h148 | h148
                  · linarith only [h131, h144, h148, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
                    · linarith only [h144, h150, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
                    · linarith only [h130, h150, hlam]
          · linarith only [h133, hlam, p0_0]
        · linarith only [h132, hc24, hlam, hphi, p0_1, u4elo3]
      · linarith only [h131, hc14, hlam, hphi, p0_1, u4elo3]
    · linarith only [h130, hc04, hlam, hphi, p0_1, u4elo3]
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

theorem n7l_sAB3_M_LI_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
      · linarith only [h0, h1, h3, hc34, hlam, hphi, u4elo4]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
      · linarith only [h0, h8, hc23, hlam, hphi, ht34, u4elo4]

theorem n7l_sAB3_M_LI_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
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
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h6, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h1, h3, h8, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h2, h3, h5, h6, hlam]
                · linarith only [h10, h5, h6, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h1, h15, h3, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                · linarith only [h17, h3, hc14, hlam, hphi, u4elo3]
                · linarith only [h17, h5, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
        · linarith only [h20, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
          · linarith only [h0, h2, h20, h22, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
            · linarith only [h1, h2, h20, h22, h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
              · linarith only [h1, h2, h20, h26, hlam]
              · linarith only [h1, h2, h22, h26, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
        · linarith only [h33, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
          · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
            · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
              · linarith only [h30, h31, h33, h37, hlam]
              · linarith only [h30, h31, h37, hc24, hlam, hphi, u4elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
              · linarith only [h0, h30, h33, h36, h40, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h0, h30, h36, h40, hc24, hlam, hphi, u4elo4]
          · linarith only [h0, h30, h35, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
      · linarith only [h0, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
        · linarith only [h30, h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
          · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
            · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
              · linarith only [h30, h46, h50, hc12, hlam, hphi, ht23, ht34, u4elo2]
              · linarith only [h30, h50, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
              · linarith only [h53, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
              · linarith only [h30, h53, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h0, h48, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem n7l_sAB3_M_LI_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have h3ehi := hb3.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, ht34, u3ehi3, u4elo4]

theorem n7l_sAB3_M_LI_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi4]
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

theorem n7l_sAB3_M_LI_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi4]
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

theorem n7l_sAB3_M_LI_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h3ehi := hb3.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
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
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, p0_1, u3ehi3, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, p0_1, u3ehi3, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi4]
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

theorem n7l_sAB3_M_LI_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB3_M_LI_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB3_M_LI_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h3ehi := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB3_M_LI_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi9]
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

theorem n7l_sAB3_M_LI_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi9]
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

theorem n7l_sAB3_M_LI_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3ehi := hb3.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
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
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, p0_1, u3ehi3, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht34, p0_1, u3ehi3, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi9]
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

theorem n7l_sAB3_M_LR_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB3_M_LR_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB3_M_LR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB3_M_LR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB3_M_LR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB3_M_LR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

end R2N4
