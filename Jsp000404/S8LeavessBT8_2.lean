import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17750000 in
theorem n8l_sBT8_H_L_H_I (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h6bigk := hb6.1
  have h6emax := hb6.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h7 | h7
    · linarith only [h7, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h9 | h9
      · rcases p0_3 (m.d 2 6) (by simp) with h10 | h10
        · rcases p0_3 (m.d 3 6) (by simp) with h11 | h11
          · rcases p0_3 (m.d 4 6) (by simp) with h12 | h12
            · rcases p0_3 (m.d 5 6) (by simp) with h13 | h13
              · rcases h6emax with h14 | h14 | h14 | h14 | h14 | h14
                · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, hlam, p0_0]
                    · linarith only [h13, h16, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h19 | h19
                    · linarith only [h19, hlam, p0_0]
                    · linarith only [h13, h19, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h14, hc06, hlam, p0_1]
                · linarith only [h10, h14, hc06, hlam, p0_1]
                · linarith only [h11, h14, hc06, hlam, p0_1]
                · linarith only [h12, h14, hc06, hlam, p0_1]
                · linarith only [h13, h14, hc06, hlam, p0_1]
              · rcases h6emax with h27 | h27 | h27 | h27 | h27 | h27
                · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h29 | h29
                    · linarith only [h29, hlam, p0_0]
                    · linarith only [h27, h28, h29, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h32 | h32
                    · linarith only [h32, hlam, p0_0]
                    · linarith only [h12, h32, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h27, hc06, hlam, p0_1]
                · linarith only [h10, h27, hc06, hlam, p0_1]
                · linarith only [h11, h27, hc06, hlam, p0_1]
                · linarith only [h12, h27, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h40 | h40
                    · linarith only [h40, hlam, p0_0]
                    · linarith only [h39, h40, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h43 | h43
                    · linarith only [h43, hlam, p0_0]
                    · linarith only [h12, h43, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h46 | h46
              · rcases h6emax with h47 | h47 | h47 | h47 | h47 | h47
                · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h49 | h49
                    · linarith only [h49, hlam, p0_0]
                    · linarith only [h46, h48, h49, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h52 | h52
                    · linarith only [h52, hlam, p0_0]
                    · linarith only [h46, h52, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h47, hc06, hlam, p0_1]
                · linarith only [h10, h47, hc06, hlam, p0_1]
                · linarith only [h11, h47, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h59 | h59
                    · linarith only [h59, hlam, p0_0]
                    · linarith only [h59, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h62 | h62
                    · linarith only [h62, hlam, p0_0]
                    · linarith only [h46, h62, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h46, h47, hc06, hlam, p0_1]
              · rcases h6emax with h66 | h66 | h66 | h66 | h66 | h66
                · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h68 | h68
                    · linarith only [h68, hlam, p0_0]
                    · linarith only [h66, h67, h68, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h71 | h71
                    · linarith only [h71, hlam, p0_0]
                    · linarith only [h11, h71, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h66, hc06, hlam, p0_1]
                · linarith only [h10, h66, hc06, hlam, p0_1]
                · linarith only [h11, h66, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h78 | h78
                    · linarith only [h78, hlam, p0_0]
                    · linarith only [h77, h78, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h81 | h81
                    · linarith only [h81, hlam, p0_0]
                    · linarith only [h11, h81, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h85 | h85
                    · linarith only [h85, hlam, p0_0]
                    · linarith only [h11, h84, h85, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h88 | h88
                    · linarith only [h88, hlam, p0_0]
                    · linarith only [h11, h88, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h91 | h91
            · rcases p0_3 (m.d 5 6) (by simp) with h92 | h92
              · rcases h6emax with h93 | h93 | h93 | h93 | h93 | h93
                · rcases m.htr 0 1 2 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h95 | h95
                    · linarith only [h95, hlam, p0_0]
                    · linarith only [h92, h95, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h98 | h98
                    · linarith only [h98, hlam, p0_0]
                    · linarith only [h92, h98, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h93, hc06, hlam, p0_1]
                · linarith only [h10, h93, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h104 | h104
                    · linarith only [h104, hlam, p0_0]
                    · linarith only [h103, h104, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h107 | h107
                    · linarith only [h107, hlam, p0_0]
                    · linarith only [h107, h92, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h91, h93, hc06, hlam, p0_1]
                · linarith only [h92, h93, hc06, hlam, p0_1]
              · rcases h6emax with h112 | h112 | h112 | h112 | h112 | h112
                · rcases m.htr 0 1 2 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h114 | h114
                    · linarith only [h114, hlam, p0_0]
                    · linarith only [h112, h113, h114, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h117 | h117
                    · linarith only [h117, hlam, p0_0]
                    · linarith only [h117, h91, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h112, hc06, hlam, p0_1]
                · linarith only [h10, h112, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h123 | h123
                    · linarith only [h123, hlam, p0_0]
                    · linarith only [h122, h123, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h126 | h126
                    · linarith only [h126, hlam, p0_0]
                    · linarith only [h126, h91, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h112, h91, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h131 | h131
                    · linarith only [h131, hlam, p0_0]
                    · linarith only [h130, h131, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h134 | h134
                    · linarith only [h134, hlam, p0_0]
                    · linarith only [h134, h91, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h137 | h137
              · rcases h6emax with h138 | h138 | h138 | h138 | h138 | h138
                · rcases m.htr 0 1 2 (by decide) (by decide) with h139 | h139
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h140 | h140
                    · linarith only [h140, hlam, p0_0]
                    · linarith only [h137, h139, h140, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h143 | h143
                    · linarith only [h143, hlam, p0_0]
                    · linarith only [h137, h143, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h138, hc06, hlam, p0_1]
                · linarith only [h10, h138, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h149 | h149
                    · linarith only [h149, hlam, p0_0]
                    · linarith only [h148, h149, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h152 | h152
                    · linarith only [h152, hlam, p0_0]
                    · linarith only [h137, h152, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h156 | h156
                    · linarith only [h156, hlam, p0_0]
                    · linarith only [h137, h155, h156, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h159 | h159
                    · linarith only [h159, hlam, p0_0]
                    · linarith only [h137, h159, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h137, h138, hc06, hlam, p0_1]
              · rcases h6emax with h163 | h163 | h163 | h163 | h163 | h163
                · rcases m.htr 0 1 2 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h165 | h165
                    · linarith only [h165, hlam, p0_0]
                    · linarith only [h163, h164, h165, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h168 | h168
                    · linarith only [h168, hlam, p0_0]
                    · linarith only [h10, h168, hc01, hc26, hlam, hphi, ht12, p0_1]
                · linarith only [h163, hc06, hlam, p0_1]
                · linarith only [h10, h163, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h173 | h173
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h174 | h174
                    · linarith only [h174, hlam, p0_0]
                    · linarith only [h174, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h177 | h177
                    · linarith only [h177, hlam, p0_0]
                    · linarith only [h10, h177, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h181 | h181
                    · linarith only [h181, hlam, p0_0]
                    · linarith only [h10, h181, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h184 | h184
                    · linarith only [h184, hlam, p0_0]
                    · linarith only [h10, h184, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h188 | h188
                    · linarith only [h188, hlam, p0_0]
                    · linarith only [h10, h187, h188, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h191 | h191
                    · linarith only [h191, hlam, p0_0]
                    · linarith only [h10, h191, hc01, hc26, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h194 | h194
          · rcases p0_3 (m.d 4 6) (by simp) with h195 | h195
            · rcases p0_3 (m.d 5 6) (by simp) with h196 | h196
              · rcases h6emax with h197 | h197 | h197 | h197 | h197 | h197
                · rcases m.htr 0 1 2 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h199 | h199
                    · linarith only [h199, hlam, p0_0]
                    · linarith only [h196, h198, h199, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h202 | h202
                    · linarith only [h202, hlam, p0_0]
                    · linarith only [h196, h202, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h197, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h207 | h207
                    · linarith only [h207, hlam, p0_0]
                    · linarith only [h206, h207, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h210 | h210
                    · linarith only [h210, hlam, p0_0]
                    · linarith only [h196, h210, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h194, h197, hc06, hlam, p0_1]
                · linarith only [h195, h197, hc06, hlam, p0_1]
                · linarith only [h196, h197, hc06, hlam, p0_1]
              · rcases h6emax with h216 | h216 | h216 | h216 | h216 | h216
                · rcases m.htr 0 1 2 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h218 | h218
                    · linarith only [h218, hlam, p0_0]
                    · linarith only [h216, h217, h218, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h221 | h221
                    · linarith only [h221, hlam, p0_0]
                    · linarith only [h195, h221, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h216, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h225 | h225
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h226 | h226
                    · linarith only [h226, hlam, p0_0]
                    · linarith only [h226, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h229 | h229
                    · linarith only [h229, hlam, p0_0]
                    · linarith only [h195, h229, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h194, h216, hc06, hlam, p0_1]
                · linarith only [h195, h216, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h235 | h235
                    · linarith only [h235, hlam, p0_0]
                    · linarith only [h234, h235, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h238 | h238
                    · linarith only [h238, hlam, p0_0]
                    · linarith only [h195, h238, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h241 | h241
              · rcases h6emax with h242 | h242 | h242 | h242 | h242 | h242
                · rcases m.htr 0 1 2 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h244 | h244
                    · linarith only [h244, hlam, p0_0]
                    · linarith only [h241, h244, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h247 | h247
                    · linarith only [h247, hlam, p0_0]
                    · linarith only [h241, h247, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h242, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h252 | h252
                    · linarith only [h252, hlam, p0_0]
                    · linarith only [h251, h252, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h255 | h255
                    · linarith only [h255, hlam, p0_0]
                    · linarith only [h241, h255, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h194, h242, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h260 | h260
                    · linarith only [h260, hlam, p0_0]
                    · linarith only [h259, h260, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h263 | h263
                    · linarith only [h263, hlam, p0_0]
                    · linarith only [h241, h263, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h241, h242, hc06, hlam, p0_1]
              · rcases h6emax with h267 | h267 | h267 | h267 | h267 | h267
                · rcases m.htr 0 1 2 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h269 | h269
                    · linarith only [h269, hlam, p0_0]
                    · linarith only [h267, h268, h269, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h272 | h272
                    · linarith only [h272, hlam, p0_0]
                    · linarith only [h194, h272, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h267, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h276 | h276
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h277 | h277
                    · linarith only [h277, hlam, p0_0]
                    · linarith only [h277, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h280 | h280
                    · linarith only [h280, hlam, p0_0]
                    · linarith only [h194, h280, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h194, h267, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h285 | h285
                    · linarith only [h285, hlam, p0_0]
                    · linarith only [h284, h285, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h288 | h288
                    · linarith only [h288, hlam, p0_0]
                    · linarith only [h194, h288, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h292 | h292
                    · linarith only [h292, hlam, p0_0]
                    · linarith only [h194, h291, h292, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h295 | h295
                    · linarith only [h295, hlam, p0_0]
                    · linarith only [h194, h295, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h298 | h298
            · rcases p0_3 (m.d 5 6) (by simp) with h299 | h299
              · rcases h6emax with h300 | h300 | h300 | h300 | h300 | h300
                · rcases m.htr 0 1 2 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h302 | h302
                    · linarith only [h302, hlam, p0_0]
                    · linarith only [h299, h302, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h305 | h305
                    · linarith only [h305, hlam, p0_0]
                    · linarith only [h299, h305, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h300, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h310 | h310
                    · linarith only [h310, hlam, p0_0]
                    · linarith only [h309, h310, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h313 | h313
                    · linarith only [h313, hlam, p0_0]
                    · linarith only [h299, h313, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h316 | h316
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h317 | h317
                    · linarith only [h317, hlam, p0_0]
                    · linarith only [h299, h316, h317, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h320 | h320
                    · linarith only [h320, hlam, p0_0]
                    · linarith only [h299, h320, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h298, h300, hc06, hlam, p0_1]
                · linarith only [h299, h300, hc06, hlam, p0_1]
              · rcases h6emax with h325 | h325 | h325 | h325 | h325 | h325
                · rcases m.htr 0 1 2 (by decide) (by decide) with h326 | h326
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h327 | h327
                    · linarith only [h327, hlam, p0_0]
                    · linarith only [h325, h326, h327, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h330 | h330
                    · linarith only [h330, hlam, p0_0]
                    · linarith only [h298, h330, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h325, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h335 | h335
                    · linarith only [h335, hlam, p0_0]
                    · linarith only [h334, h335, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h338 | h338
                    · linarith only [h338, hlam, p0_0]
                    · linarith only [h298, h338, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h341 | h341
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h342 | h342
                    · linarith only [h342, hlam, p0_0]
                    · linarith only [h298, h341, h342, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h345 | h345
                    · linarith only [h345, hlam, p0_0]
                    · linarith only [h298, h345, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h298, h325, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h350 | h350
                    · linarith only [h350, hlam, p0_0]
                    · linarith only [h349, h350, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h353 | h353
                    · linarith only [h353, hlam, p0_0]
                    · linarith only [h298, h353, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h356 | h356
              · rcases h6emax with h357 | h357 | h357 | h357 | h357 | h357
                · rcases m.htr 0 1 2 (by decide) (by decide) with h358 | h358
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h359 | h359
                    · linarith only [h359, hlam, p0_0]
                    · linarith only [h356, h358, h359, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h362 | h362
                    · linarith only [h362, hlam, p0_0]
                    · linarith only [h356, h362, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h357, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h367 | h367
                    · linarith only [h367, hlam, p0_0]
                    · linarith only [h367, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h370 | h370
                    · linarith only [h370, hlam, p0_0]
                    · linarith only [h356, h370, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h374 | h374
                    · linarith only [h374, hlam, p0_0]
                    · linarith only [h356, h373, h374, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h377 | h377
                    · linarith only [h377, hlam, p0_0]
                    · linarith only [h356, h377, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h381 | h381
                    · linarith only [h381, hlam, p0_0]
                    · linarith only [h356, h381, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h384 | h384
                    · linarith only [h384, hlam, p0_0]
                    · linarith only [h356, h384, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h356, h357, hc06, hlam, p0_1]
              · rcases h6emax with h388 | h388 | h388 | h388 | h388 | h388
                · rcases m.htr 0 1 2 (by decide) (by decide) with h389 | h389
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h390 | h390
                    · linarith only [h390, hlam, p0_0]
                    · linarith only [h390, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h393 | h393
                    · linarith only [h393, hlam, p0_0]
                    · linarith only [h393, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h388, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h397 | h397
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h398 | h398
                    · linarith only [h398, hlam, p0_0]
                    · linarith only [h398, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h401 | h401
                    · linarith only [h401, hlam, p0_0]
                    · linarith only [h401, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h405 | h405
                    · linarith only [h405, hlam, p0_0]
                    · linarith only [h405, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h408 | h408
                    · linarith only [h408, hlam, p0_0]
                    · linarith only [h408, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h412 | h412
                    · linarith only [h412, hlam, p0_0]
                    · linarith only [h411, h412, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h415 | h415
                    · linarith only [h415, hlam, p0_0]
                    · linarith only [h415, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h418 | h418
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h419 | h419
                    · linarith only [h419, hlam, p0_0]
                    · linarith only [h418, h419, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h422 | h422
                    · linarith only [h422, hlam, p0_0]
                    · linarith only [h422, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h9, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h427 | h427
    · linarith only [h427, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h429 | h429
      · rcases p0_3 (m.d 2 6) (by simp) with h430 | h430
        · linarith only [h430, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h432 | h432
          · rcases p0_3 (m.d 4 6) (by simp) with h433 | h433
            · rcases p0_3 (m.d 5 6) (by simp) with h434 | h434
              · rcases h6emax with h435 | h435 | h435 | h435 | h435 | h435
                · rcases m.htr 0 1 2 (by decide) (by decide) with h436 | h436
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h437 | h437
                    · linarith only [h437, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h437, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h440 | h440
                    · linarith only [h427, h440, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h440, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h435, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h445 | h445
                    · linarith only [h427, h445, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h445, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h448 | h448
                    · linarith only [h427, h444, h448, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h448, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h432, h435, hc06, hlam, p0_1]
                · linarith only [h427, h433, h435, hc06, hlam, p0_1]
                · linarith only [h427, h434, h435, hc06, hlam, p0_1]
              · rcases h6emax with h454 | h454 | h454 | h454 | h454 | h454
                · rcases m.htr 0 1 2 (by decide) (by decide) with h455 | h455
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h456 | h456
                    · linarith only [h456, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h456, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h459 | h459
                    · linarith only [h427, h455, h459, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h459, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h454, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h463 | h463
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h464 | h464
                    · linarith only [h427, h464, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h463, h464, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h467 | h467
                    · linarith only [h427, h463, h467, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h467, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h432, h454, hc06, hlam, p0_1]
                · linarith only [h427, h433, h454, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h472 | h472
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h473 | h473
                    · linarith only [h427, h473, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h472, h473, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h476 | h476
                    · linarith only [h427, h472, h476, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h476, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h479 | h479
              · rcases h6emax with h480 | h480 | h480 | h480 | h480 | h480
                · rcases m.htr 0 1 2 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h482 | h482
                    · linarith only [h427, h482, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h480, h481, h482, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h485 | h485
                    · linarith only [h427, h481, h485, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h485, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h480, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h490 | h490
                    · linarith only [h427, h490, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h489, h490, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h493 | h493
                    · linarith only [h427, h489, h493, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h493, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h432, h480, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h497 | h497
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h498 | h498
                    · linarith only [h427, h498, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h498, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h501 | h501
                    · linarith only [h427, h497, h501, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h501, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h479, h480, hc06, hlam, p0_1]
              · rcases h6emax with h505 | h505 | h505 | h505 | h505 | h505
                · rcases m.htr 0 1 2 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h507 | h507
                    · linarith only [h427, h507, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h507, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h510 | h510
                    · linarith only [h427, h506, h510, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h510, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h505, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h514 | h514
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h515 | h515
                    · linarith only [h427, h515, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h514, h515, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h518 | h518
                    · linarith only [h427, h514, h518, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h518, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h432, h505, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h522 | h522
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h523 | h523
                    · linarith only [h427, h523, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h523, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h526 | h526
                    · linarith only [h427, h522, h526, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h526, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h529 | h529
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h530 | h530
                    · linarith only [h427, h530, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h530, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h533 | h533
                    · linarith only [h427, h529, h533, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h533, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h536 | h536
            · rcases p0_3 (m.d 5 6) (by simp) with h537 | h537
              · rcases h6emax with h538 | h538 | h538 | h538 | h538 | h538
                · rcases m.htr 0 1 2 (by decide) (by decide) with h539 | h539
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h540 | h540
                    · linarith only [h427, h540, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h540, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h543 | h543
                    · linarith only [h427, h539, h543, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h543, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h538, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h548 | h548
                    · linarith only [h427, h548, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h547, h548, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h551 | h551
                    · linarith only [h427, h551, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h551, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h555 | h555
                    · linarith only [h427, h555, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h555, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h558 | h558
                    · linarith only [h427, h554, h558, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h558, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h536, h538, hc06, hlam, p0_1]
                · linarith only [h427, h537, h538, hc06, hlam, p0_1]
              · rcases h6emax with h563 | h563 | h563 | h563 | h563 | h563
                · rcases m.htr 0 1 2 (by decide) (by decide) with h564 | h564
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h565 | h565
                    · linarith only [h427, h565, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h563, h564, h565, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h568 | h568
                    · linarith only [h427, h564, h568, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h568, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h563, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h572 | h572
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h573 | h573
                    · linarith only [h427, h573, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h573, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h576 | h576
                    · linarith only [h427, h572, h576, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h576, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h579 | h579
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h580 | h580
                    · linarith only [h427, h580, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h580, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h583 | h583
                    · linarith only [h427, h579, h583, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h583, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h536, h563, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h587 | h587
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h588 | h588
                    · linarith only [h427, h588, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h587, h588, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h591 | h591
                    · linarith only [h427, h587, h591, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h591, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h594 | h594
              · rcases h6emax with h595 | h595 | h595 | h595 | h595 | h595
                · rcases m.htr 0 1 2 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h597 | h597
                    · linarith only [h427, h597, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h597, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h600 | h600
                    · linarith only [h427, h596, h600, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h600, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h595, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h605 | h605
                    · linarith only [h427, h605, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h605, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h608 | h608
                    · linarith only [h427, h604, h608, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h608, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h611 | h611
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h612 | h612
                    · linarith only [h427, h612, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h612, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h615 | h615
                    · linarith only [h427, h611, h615, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h615, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h618 | h618
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h619 | h619
                    · linarith only [h427, h619, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h619, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h622 | h622
                    · linarith only [h427, h618, h622, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h622, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h594, h595, hc06, hlam, p0_1]
              · rcases h6emax with h626 | h626 | h626 | h626 | h626 | h626
                · rcases m.htr 0 1 2 (by decide) (by decide) with h627 | h627
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h628 | h628
                    · linarith only [h427, h628, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h628, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h631 | h631
                    · linarith only [h427, h627, h631, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h631, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h427, h626, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h635 | h635
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h636 | h636
                    · linarith only [h427, h636, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h636, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h639 | h639
                    · linarith only [h427, h635, h639, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h639, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h642 | h642
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h643 | h643
                    · linarith only [h427, h643, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h642, h643, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h646 | h646
                    · linarith only [h427, h642, h646, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h646, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h649 | h649
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h650 | h650
                    · linarith only [h427, h650, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h649, h650, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h653 | h653
                    · linarith only [h427, h653, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h653, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h656 | h656
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h657 | h657
                    · linarith only [h427, h657, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h427, h657, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h660 | h660
                    · linarith only [h427, h656, h660, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h427, h660, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h429, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h664 | h664
    · linarith only [h664, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h666 | h666
      · rcases p0_3 (m.d 2 6) (by simp) with h667 | h667
        · rcases p0_3 (m.d 3 6) (by simp) with h668 | h668
          · linarith only [h668, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h670 | h670
            · rcases p0_3 (m.d 5 6) (by simp) with h671 | h671
              · rcases h6emax with h672 | h672 | h672 | h672 | h672 | h672
                · rcases m.htr 0 1 2 (by decide) (by decide) with h673 | h673
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h674 | h674
                    · linarith only [h674, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h674, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h677 | h677
                    · linarith only [h664, h673, h677, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h677, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h672, hc06, hlam, p0_1]
                · linarith only [h664, h667, h672, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h682 | h682
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h683 | h683
                    · linarith only [h664, h683, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h683, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h686 | h686
                    · linarith only [h664, h682, h686, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h686, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h670, h672, hc06, hlam, p0_1]
                · linarith only [h664, h671, h672, hc06, hlam, p0_1]
              · rcases h6emax with h691 | h691 | h691 | h691 | h691 | h691
                · rcases m.htr 0 1 2 (by decide) (by decide) with h692 | h692
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h693 | h693
                    · linarith only [h693, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h693, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h696 | h696
                    · linarith only [h664, h692, h696, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h696, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h691, hc06, hlam, p0_1]
                · linarith only [h664, h667, h691, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h701 | h701
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h702 | h702
                    · linarith only [h664, h702, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h702, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h705 | h705
                    · linarith only [h664, h701, h705, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h705, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h670, h691, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h709 | h709
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h710 | h710
                    · linarith only [h664, h710, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h709, h710, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h713 | h713
                    · linarith only [h664, h709, h713, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h713, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h716 | h716
              · rcases h6emax with h717 | h717 | h717 | h717 | h717 | h717
                · rcases m.htr 0 1 2 (by decide) (by decide) with h718 | h718
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h719 | h719
                    · linarith only [h664, h719, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h717, h718, h719, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h722 | h722
                    · linarith only [h664, h718, h722, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h722, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h717, hc06, hlam, p0_1]
                · linarith only [h664, h667, h717, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h727 | h727
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h728 | h728
                    · linarith only [h664, h728, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h728, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h731 | h731
                    · linarith only [h664, h727, h731, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h731, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h734 | h734
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h735 | h735
                    · linarith only [h664, h735, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h735, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h738 | h738
                    · linarith only [h664, h734, h738, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h738, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h716, h717, hc06, hlam, p0_1]
              · rcases h6emax with h742 | h742 | h742 | h742 | h742 | h742
                · rcases m.htr 0 1 2 (by decide) (by decide) with h743 | h743
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h744 | h744
                    · linarith only [h664, h744, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h744, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h747 | h747
                    · linarith only [h664, h743, h747, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h747, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h742, hc06, hlam, p0_1]
                · linarith only [h664, h667, h742, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h752 | h752
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h753 | h753
                    · linarith only [h664, h753, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h753, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h756 | h756
                    · linarith only [h664, h752, h756, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h756, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h759 | h759
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h760 | h760
                    · linarith only [h664, h760, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h759, h760, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h763 | h763
                    · linarith only [h664, h763, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h763, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h766 | h766
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h767 | h767
                    · linarith only [h664, h767, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h766, h767, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h770 | h770
                    · linarith only [h664, h766, h770, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h770, hc01, hc16, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h773 | h773
          · linarith only [h773, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h775 | h775
            · rcases p0_3 (m.d 5 6) (by simp) with h776 | h776
              · rcases h6emax with h777 | h777 | h777 | h777 | h777 | h777
                · rcases m.htr 0 1 2 (by decide) (by decide) with h778 | h778
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h779 | h779
                    · linarith only [h664, h779, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h777, h778, h779, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h782 | h782
                    · linarith only [h664, h778, h782, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h782, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h777, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h786 | h786
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h787 | h787
                    · linarith only [h664, h787, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h787, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h790 | h790
                    · linarith only [h664, h786, h790, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h790, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h793 | h793
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h794 | h794
                    · linarith only [h664, h794, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h794, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h797 | h797
                    · linarith only [h664, h793, h797, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h797, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h775, h777, hc06, hlam, p0_1]
                · linarith only [h664, h776, h777, hc06, hlam, p0_1]
              · rcases h6emax with h802 | h802 | h802 | h802 | h802 | h802
                · rcases m.htr 0 1 2 (by decide) (by decide) with h803 | h803
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h804 | h804
                    · linarith only [h664, h804, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h804, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h807 | h807
                    · linarith only [h664, h803, h807, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h807, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h802, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h811 | h811
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h812 | h812
                    · linarith only [h664, h812, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h812, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h815 | h815
                    · linarith only [h664, h811, h815, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h815, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h818 | h818
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h819 | h819
                    · linarith only [h664, h819, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h819, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h822 | h822
                    · linarith only [h664, h818, h822, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h822, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h775, h802, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h826 | h826
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h827 | h827
                    · linarith only [h664, h827, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h827, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h830 | h830
                    · linarith only [h664, h826, h830, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h830, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h833 | h833
              · rcases h6emax with h834 | h834 | h834 | h834 | h834 | h834
                · rcases m.htr 0 1 2 (by decide) (by decide) with h835 | h835
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h836 | h836
                    · linarith only [h664, h836, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h834, h835, h836, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h839 | h839
                    · linarith only [h664, h839, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h839, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h834, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h843 | h843
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h844 | h844
                    · linarith only [h664, h844, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h843, h844, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h847 | h847
                    · linarith only [h664, h843, h847, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h847, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h851 | h851
                    · linarith only [h664, h851, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h850, h851, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h854 | h854
                    · linarith only [h664, h850, h854, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h854, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h857 | h857
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h858 | h858
                    · linarith only [h664, h858, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h858, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h861 | h861
                    · linarith only [h664, h857, h861, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h861, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h833, h834, hc06, hlam, p0_1]
              · rcases h6emax with h865 | h865 | h865 | h865 | h865 | h865
                · rcases m.htr 0 1 2 (by decide) (by decide) with h866 | h866
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h867 | h867
                    · linarith only [h664, h867, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h867, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h870 | h870
                    · linarith only [h664, h866, h870, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h870, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h664, h865, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h875 | h875
                    · linarith only [h664, h875, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h874, h875, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h878 | h878
                    · linarith only [h664, h878, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h878, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h881 | h881
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h882 | h882
                    · linarith only [h664, h882, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h882, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h885 | h885
                    · linarith only [h664, h881, h885, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h885, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h888 | h888
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h889 | h889
                    · linarith only [h664, h889, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h889, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h892 | h892
                    · linarith only [h664, h888, h892, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h664, h892, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h896 | h896
                    · linarith only [h664, h896, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h895, h896, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h899 | h899
                    · linarith only [h664, h899, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h664, h899, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h666, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h903 | h903
    · linarith only [h903, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h905 | h905
      · rcases p0_3 (m.d 2 6) (by simp) with h906 | h906
        · rcases p0_3 (m.d 3 6) (by simp) with h907 | h907
          · rcases p0_3 (m.d 4 6) (by simp) with h908 | h908
            · linarith only [h908, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h910 | h910
              · rcases h6emax with h911 | h911 | h911 | h911 | h911 | h911
                · rcases m.htr 0 1 2 (by decide) (by decide) with h912 | h912
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h913 | h913
                    · linarith only [h913, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h911, h912, h913, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h916 | h916
                    · linarith only [h903, h912, h916, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h916, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h903, h911, hc06, hlam, p0_1]
                · linarith only [h903, h906, h911, hc06, hlam, p0_1]
                · linarith only [h903, h907, h911, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h922 | h922
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h923 | h923
                    · linarith only [h903, h923, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h923, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h926 | h926
                    · linarith only [h903, h922, h926, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h926, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h903, h910, h911, hc06, hlam, p0_1]
              · rcases h6emax with h930 | h930 | h930 | h930 | h930 | h930
                · rcases m.htr 0 1 2 (by decide) (by decide) with h931 | h931
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h932 | h932
                    · linarith only [h903, h932, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h932, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h935 | h935
                    · linarith only [h903, h931, h935, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h935, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h903, h930, hc06, hlam, p0_1]
                · linarith only [h903, h906, h930, hc06, hlam, p0_1]
                · linarith only [h903, h907, h930, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h941 | h941
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h942 | h942
                    · linarith only [h903, h942, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h941, h942, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h945 | h945
                    · linarith only [h903, h945, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h945, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h948 | h948
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h949 | h949
                    · linarith only [h903, h949, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h948, h949, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h952 | h952
                    · linarith only [h903, h952, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h952, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h955 | h955
            · linarith only [h955, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h957 | h957
              · rcases h6emax with h958 | h958 | h958 | h958 | h958 | h958
                · rcases m.htr 0 1 2 (by decide) (by decide) with h959 | h959
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h960 | h960
                    · linarith only [h903, h960, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h958, h959, h960, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h963 | h963
                    · linarith only [h903, h959, h963, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h963, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h903, h958, hc06, hlam, p0_1]
                · linarith only [h903, h906, h958, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h968 | h968
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h969 | h969
                    · linarith only [h903, h969, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h968, h969, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h972 | h972
                    · linarith only [h903, h968, h972, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h972, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h975 | h975
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h976 | h976
                    · linarith only [h903, h976, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h976, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h979 | h979
                    · linarith only [h903, h975, h979, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h979, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h903, h957, h958, hc06, hlam, p0_1]
              · rcases h6emax with h983 | h983 | h983 | h983 | h983 | h983
                · rcases m.htr 0 1 2 (by decide) (by decide) with h984 | h984
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h985 | h985
                    · linarith only [h985, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h985, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h988 | h988
                    · linarith only [h903, h984, h988, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h988, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h903, h983, hc06, hlam, p0_1]
                · linarith only [h903, h906, h983, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h993 | h993
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h994 | h994
                    · linarith only [h903, h994, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h903, h993, h994, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h997 | h997
                    · linarith only [h903, h993, h997, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h903, h997, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1000 | h1000
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1001 | h1001
                    · linarith only [h1001, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1001, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1004 | h1004
                    · linarith only [h1000, h1004, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1004, h903, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1007 | h1007
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1008 | h1008
                    · linarith only [h1008, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1007, h1008, h903, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1011 | h1011
                    · linarith only [h1007, h1011, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1011, h903, hc01, hc16, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h1014 | h1014
          · rcases p0_3 (m.d 4 6) (by simp) with h1015 | h1015
            · linarith only [h1015, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1017 | h1017
              · rcases h6emax with h1018 | h1018 | h1018 | h1018 | h1018 | h1018
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1019 | h1019
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1020 | h1020
                    · linarith only [h1020, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1020, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1023 | h1023
                    · linarith only [h1019, h1023, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1023, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1018, h903, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1027 | h1027
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1028 | h1028
                    · linarith only [h1028, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1028, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1031 | h1031
                    · linarith only [h1027, h1031, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1031, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1014, h1018, h903, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1035 | h1035
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1036 | h1036
                    · linarith only [h1036, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1035, h1036, h903, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1039 | h1039
                    · linarith only [h1035, h1039, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1039, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1017, h1018, h903, hc06, hlam, p0_1]
              · rcases h6emax with h1043 | h1043 | h1043 | h1043 | h1043 | h1043
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1044 | h1044
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1045 | h1045
                    · linarith only [h1045, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1043, h1044, h1045, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1048 | h1048
                    · linarith only [h1044, h1048, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1048, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1043, h903, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1052 | h1052
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1053 | h1053
                    · linarith only [h1053, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1052, h1053, h903, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1056 | h1056
                    · linarith only [h1052, h1056, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1056, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1014, h1043, h903, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1060 | h1060
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1061 | h1061
                    · linarith only [h1061, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1061, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1064 | h1064
                    · linarith only [h1060, h1064, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1064, h903, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1067 | h1067
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1068 | h1068
                    · linarith only [h1068, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1068, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1071 | h1071
                    · linarith only [h1067, h1071, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1071, h903, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h1074 | h1074
            · linarith only [h1074, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h1076 | h1076
              · rcases h6emax with h1077 | h1077 | h1077 | h1077 | h1077 | h1077
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1078 | h1078
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1079 | h1079
                    · linarith only [h1079, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1079, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1082 | h1082
                    · linarith only [h1078, h1082, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1082, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1077, h903, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1086 | h1086
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1087 | h1087
                    · linarith only [h1087, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1087, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1090 | h1090
                    · linarith only [h1086, h1090, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1090, h903, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1093 | h1093
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1094 | h1094
                    · linarith only [h1094, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1094, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1097 | h1097
                    · linarith only [h1093, h1097, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1097, h903, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1100 | h1100
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1101 | h1101
                    · linarith only [h1101, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1101, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1104 | h1104
                    · linarith only [h1100, h1104, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1104, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1076, h1077, h903, hc06, hlam, p0_1]
              · rcases h6emax with h1108 | h1108 | h1108 | h1108 | h1108 | h1108
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1109 | h1109
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1110 | h1110
                    · linarith only [h1110, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1110, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1113 | h1113
                    · linarith only [h1109, h1113, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1113, h903, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1108, h903, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1117 | h1117
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1118 | h1118
                    · linarith only [h1118, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1118, h903, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1121 | h1121
                    · linarith only [h1117, h1121, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1121, h903, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1125 | h1125
                    · linarith only [h1125, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1124, h1125, h903, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1128 | h1128
                    · linarith only [h1124, h1128, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1128, h903, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1131 | h1131
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1132 | h1132
                    · linarith only [h1132, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1131, h1132, h903, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1135 | h1135
                    · linarith only [h1135, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1135, h903, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1138 | h1138
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1139 | h1139
                    · linarith only [h1139, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1138, h1139, h903, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1142 | h1142
                    · linarith only [h1138, h1142, h903, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1142, h903, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h905, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1146 | h1146
    · linarith only [h1146, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1148 | h1148
      · rcases p0_3 (m.d 2 6) (by simp) with h1149 | h1149
        · rcases p0_3 (m.d 3 6) (by simp) with h1150 | h1150
          · rcases p0_3 (m.d 4 6) (by simp) with h1151 | h1151
            · rcases p0_3 (m.d 5 6) (by simp) with h1152 | h1152
              · linarith only [h1152, hlam, p0_0]
              · rcases h6emax with h1154 | h1154 | h1154 | h1154 | h1154 | h1154
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1155 | h1155
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1156 | h1156
                    · linarith only [h1156, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1156, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1159 | h1159
                    · linarith only [h1146, h1155, h1159, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1159, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1154, hc06, hlam, p0_1]
                · linarith only [h1146, h1149, h1154, hc06, hlam, p0_1]
                · linarith only [h1146, h1150, h1154, hc06, hlam, p0_1]
                · linarith only [h1146, h1151, h1154, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1166 | h1166
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1167 | h1167
                    · linarith only [h1146, h1167, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1167, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1170 | h1170
                    · linarith only [h1146, h1166, h1170, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1170, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1173 | h1173
              · linarith only [h1173, hlam, p0_0]
              · rcases h6emax with h1175 | h1175 | h1175 | h1175 | h1175 | h1175
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1176 | h1176
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1177 | h1177
                    · linarith only [h1146, h1177, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1177, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1180 | h1180
                    · linarith only [h1146, h1176, h1180, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1180, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1175, hc06, hlam, p0_1]
                · linarith only [h1146, h1149, h1175, hc06, hlam, p0_1]
                · linarith only [h1146, h1150, h1175, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1186 | h1186
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1187 | h1187
                    · linarith only [h1146, h1187, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1186, h1187, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1190 | h1190
                    · linarith only [h1146, h1190, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1190, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1193 | h1193
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1194 | h1194
                    · linarith only [h1146, h1194, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1194, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1197 | h1197
                    · linarith only [h1146, h1193, h1197, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1197, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h1200 | h1200
            · rcases p0_3 (m.d 5 6) (by simp) with h1201 | h1201
              · linarith only [h1201, hlam, p0_0]
              · rcases h6emax with h1203 | h1203 | h1203 | h1203 | h1203 | h1203
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1205 | h1205
                    · linarith only [h1146, h1205, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1203, h1204, h1205, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1208 | h1208
                    · linarith only [h1146, h1204, h1208, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1208, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1203, hc06, hlam, p0_1]
                · linarith only [h1146, h1149, h1203, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1213 | h1213
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1214 | h1214
                    · linarith only [h1146, h1214, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1213, h1214, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1217 | h1217
                    · linarith only [h1146, h1213, h1217, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1217, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1200, h1203, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1221 | h1221
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1222 | h1222
                    · linarith only [h1146, h1222, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1221, h1222, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1225 | h1225
                    · linarith only [h1146, h1221, h1225, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1225, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1228 | h1228
              · linarith only [h1228, hlam, p0_0]
              · rcases h6emax with h1230 | h1230 | h1230 | h1230 | h1230 | h1230
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1231 | h1231
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1232 | h1232
                    · linarith only [h1146, h1232, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1232, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1235 | h1235
                    · linarith only [h1146, h1231, h1235, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1235, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1230, hc06, hlam, p0_1]
                · linarith only [h1146, h1149, h1230, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1240 | h1240
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1241 | h1241
                    · linarith only [h1146, h1241, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1241, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1244 | h1244
                    · linarith only [h1146, h1240, h1244, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1244, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1247 | h1247
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1248 | h1248
                    · linarith only [h1146, h1248, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1247, h1248, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1251 | h1251
                    · linarith only [h1146, h1251, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1251, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1254 | h1254
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1255 | h1255
                    · linarith only [h1146, h1255, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1255, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1258 | h1258
                    · linarith only [h1146, h1254, h1258, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1258, hc01, hc16, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 6) (by simp) with h1261 | h1261
          · rcases p0_3 (m.d 4 6) (by simp) with h1262 | h1262
            · rcases p0_3 (m.d 5 6) (by simp) with h1263 | h1263
              · linarith only [h1263, hlam, p0_0]
              · rcases h6emax with h1265 | h1265 | h1265 | h1265 | h1265 | h1265
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1266 | h1266
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1267 | h1267
                    · linarith only [h1146, h1267, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1265, h1266, h1267, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1270 | h1270
                    · linarith only [h1146, h1266, h1270, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1270, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1265, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1274 | h1274
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1275 | h1275
                    · linarith only [h1146, h1275, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1275, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1278 | h1278
                    · linarith only [h1146, h1274, h1278, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1278, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1261, h1265, hc06, hlam, p0_1]
                · linarith only [h1146, h1262, h1265, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1283 | h1283
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1284 | h1284
                    · linarith only [h1146, h1284, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1284, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1287 | h1287
                    · linarith only [h1146, h1283, h1287, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1287, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1290 | h1290
              · linarith only [h1290, hlam, p0_0]
              · rcases h6emax with h1292 | h1292 | h1292 | h1292 | h1292 | h1292
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1293 | h1293
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1294 | h1294
                    · linarith only [h1146, h1294, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1294, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1297 | h1297
                    · linarith only [h1146, h1293, h1297, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1297, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1292, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1301 | h1301
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1302 | h1302
                    · linarith only [h1146, h1302, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1302, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1305 | h1305
                    · linarith only [h1146, h1301, h1305, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1305, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1261, h1292, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1309 | h1309
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1310 | h1310
                    · linarith only [h1146, h1310, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1310, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1313 | h1313
                    · linarith only [h1146, h1309, h1313, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1313, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1316 | h1316
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1317 | h1317
                    · linarith only [h1146, h1317, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1317, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1320 | h1320
                    · linarith only [h1146, h1316, h1320, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1320, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h1323 | h1323
            · rcases p0_3 (m.d 5 6) (by simp) with h1324 | h1324
              · linarith only [h1324, hlam, p0_0]
              · rcases h6emax with h1326 | h1326 | h1326 | h1326 | h1326 | h1326
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1327 | h1327
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1328 | h1328
                    · linarith only [h1146, h1328, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1326, h1327, h1328, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1331 | h1331
                    · linarith only [h1146, h1327, h1331, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1331, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1326, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1335 | h1335
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1336 | h1336
                    · linarith only [h1146, h1336, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1336, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1339 | h1339
                    · linarith only [h1146, h1335, h1339, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1339, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1342 | h1342
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1343 | h1343
                    · linarith only [h1146, h1343, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1342, h1343, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1346 | h1346
                    · linarith only [h1146, h1342, h1346, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1346, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1323, h1326, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1350 | h1350
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1351 | h1351
                    · linarith only [h1146, h1351, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1350, h1351, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1354 | h1354
                    · linarith only [h1146, h1350, h1354, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1354, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1357 | h1357
              · linarith only [h1357, hlam, p0_0]
              · rcases h6emax with h1359 | h1359 | h1359 | h1359 | h1359 | h1359
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1360 | h1360
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1361 | h1361
                    · linarith only [h1146, h1361, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1359, h1360, h1361, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1364 | h1364
                    · linarith only [h1146, h1360, h1364, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1364, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1146, h1359, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1368 | h1368
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1369 | h1369
                    · linarith only [h1146, h1369, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1369, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1372 | h1372
                    · linarith only [h1146, h1368, h1372, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1372, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1375 | h1375
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1376 | h1376
                    · linarith only [h1146, h1376, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1375, h1376, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1379 | h1379
                    · linarith only [h1146, h1375, h1379, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1379, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1382 | h1382
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1383 | h1383
                    · linarith only [h1146, h1383, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1382, h1383, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1386 | h1386
                    · linarith only [h1146, h1386, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1386, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1389 | h1389
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1390 | h1390
                    · linarith only [h1146, h1390, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1146, h1390, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1393 | h1393
                    · linarith only [h1146, h1389, h1393, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1146, h1393, hc01, hc16, hlam, hphi, p0_1]
      · linarith only [h1148, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1397 | h1397
    · linarith only [h1397, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h1399 | h1399
      · rcases p0_3 (m.d 2 6) (by simp) with h1400 | h1400
        · rcases p0_3 (m.d 3 6) (by simp) with h1401 | h1401
          · rcases p0_3 (m.d 4 6) (by simp) with h1402 | h1402
            · rcases p0_3 (m.d 5 6) (by simp) with h1403 | h1403
              · rcases h6emax with h1404 | h1404 | h1404 | h1404 | h1404 | h1404
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1405 | h1405
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1406 | h1406
                    · linarith only [h1399, h1406, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1404, h1405, h1406, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1409 | h1409
                    · linarith only [h1399, h1409, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1409, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1404, hc06, hlam, p0_1]
                · linarith only [h1404, hc06, hlam, p0_1]
                · linarith only [h1401, h1404, hc06, hlam, p0_1]
                · linarith only [h1402, h1404, hc06, hlam, p0_1]
                · linarith only [h1403, h1404, hc06, hlam, p0_1]
              · rcases h6emax with h1417 | h1417 | h1417 | h1417 | h1417 | h1417
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1418 | h1418
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1419 | h1419
                    · linarith only [h1399, h1419, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1417, h1418, h1419, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1422 | h1422
                    · linarith only [h1399, h1422, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1422, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1417, hc06, hlam, p0_1]
                · linarith only [h1417, hc06, hlam, p0_1]
                · linarith only [h1401, h1417, hc06, hlam, p0_1]
                · linarith only [h1402, h1417, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1429 | h1429
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1430 | h1430
                    · linarith only [h1399, h1430, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1430, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1433 | h1433
                    · linarith only [h1399, h1433, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1433, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1436 | h1436
              · rcases h6emax with h1437 | h1437 | h1437 | h1437 | h1437 | h1437
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1438 | h1438
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1439 | h1439
                    · linarith only [h1399, h1439, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1439, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1442 | h1442
                    · linarith only [h1399, h1438, h1442, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1442, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1437, hc06, hlam, p0_1]
                · linarith only [h1437, hc06, hlam, p0_1]
                · linarith only [h1401, h1437, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1448 | h1448
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1449 | h1449
                    · linarith only [h1399, h1449, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1448, h1449, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1452 | h1452
                    · linarith only [h1399, h1452, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1452, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1436, h1437, hc06, hlam, p0_1]
              · rcases h6emax with h1456 | h1456 | h1456 | h1456 | h1456 | h1456
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1457 | h1457
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1458 | h1458
                    · linarith only [h1399, h1458, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1456, h1457, h1458, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1461 | h1461
                    · linarith only [h1399, h1457, h1461, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1461, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1456, hc06, hlam, p0_1]
                · linarith only [h1456, hc06, hlam, p0_1]
                · linarith only [h1401, h1456, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1467 | h1467
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1468 | h1468
                    · linarith only [h1399, h1468, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1468, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1471 | h1471
                    · linarith only [h1399, h1467, h1471, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1471, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1474 | h1474
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1475 | h1475
                    · linarith only [h1399, h1475, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1475, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1478 | h1478
                    · linarith only [h1399, h1478, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1478, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h1481 | h1481
            · rcases p0_3 (m.d 5 6) (by simp) with h1482 | h1482
              · rcases h6emax with h1483 | h1483 | h1483 | h1483 | h1483 | h1483
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1484 | h1484
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1485 | h1485
                    · linarith only [h1399, h1485, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1483, h1484, h1485, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1488 | h1488
                    · linarith only [h1399, h1488, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1488, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1483, hc06, hlam, p0_1]
                · linarith only [h1483, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1493 | h1493
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1494 | h1494
                    · linarith only [h1399, h1494, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1493, h1494, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1497 | h1497
                    · linarith only [h1399, h1497, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1497, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1481, h1483, hc06, hlam, p0_1]
                · linarith only [h1482, h1483, hc06, hlam, p0_1]
              · rcases h6emax with h1502 | h1502 | h1502 | h1502 | h1502 | h1502
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1503 | h1503
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1504 | h1504
                    · linarith only [h1399, h1504, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1502, h1503, h1504, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1507 | h1507
                    · linarith only [h1399, h1503, h1507, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1507, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1502, hc06, hlam, p0_1]
                · linarith only [h1502, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1512 | h1512
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1513 | h1513
                    · linarith only [h1399, h1513, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1513, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1516 | h1516
                    · linarith only [h1399, h1512, h1516, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1516, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1481, h1502, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1520 | h1520
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1521 | h1521
                    · linarith only [h1399, h1521, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1521, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1524 | h1524
                    · linarith only [h1399, h1520, h1524, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1524, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1527 | h1527
              · rcases h6emax with h1528 | h1528 | h1528 | h1528 | h1528 | h1528
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1529 | h1529
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1530 | h1530
                    · linarith only [h1399, h1530, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1530, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1533 | h1533
                    · linarith only [h1399, h1529, h1533, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1533, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1528, hc06, hlam, p0_1]
                · linarith only [h1528, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1538 | h1538
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1539 | h1539
                    · linarith only [h1399, h1539, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1539, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1542 | h1542
                    · linarith only [h1399, h1538, h1542, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1542, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1545 | h1545
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1546 | h1546
                    · linarith only [h1399, h1546, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1546, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1549 | h1549
                    · linarith only [h1399, h1545, h1549, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1549, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1527, h1528, hc06, hlam, p0_1]
              · rcases h6emax with h1553 | h1553 | h1553 | h1553 | h1553 | h1553
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1554 | h1554
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1555 | h1555
                    · linarith only [h1399, h1555, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1553, h1554, h1555, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1558 | h1558
                    · linarith only [h1399, h1554, h1558, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1558, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h1399, h1553, hc06, hlam, p0_1]
                · linarith only [h1553, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1563 | h1563
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1564 | h1564
                    · linarith only [h1399, h1564, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1563, h1564, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1567 | h1567
                    · linarith only [h1399, h1563, h1567, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h1399, h1567, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1570 | h1570
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1571 | h1571
                    · linarith only [h1399, h1571, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1571, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1574 | h1574
                    · linarith only [h1399, h1574, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1574, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1577 | h1577
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1578 | h1578
                    · linarith only [h1399, h1578, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1578, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1581 | h1581
                    · linarith only [h1399, h1581, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h1399, h1581, hc01, hc16, hlam, hphi, p0_1]
        · linarith only [h1400, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1585 | h1585
        · rcases p0_3 (m.d 3 6) (by simp) with h1586 | h1586
          · rcases p0_3 (m.d 4 6) (by simp) with h1587 | h1587
            · rcases p0_3 (m.d 5 6) (by simp) with h1588 | h1588
              · rcases h6emax with h1589 | h1589 | h1589 | h1589 | h1589 | h1589
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1590 | h1590
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1591 | h1591
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1592 | h1592
                      · linarith only [h1592, hlam, p0_0]
                      · linarith only [h1588, h1592, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1591, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1596 | h1596
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1597 | h1597
                      · linarith only [h1597, hlam, p0_0]
                      · linarith only [h1588, h1590, h1597, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1596, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1601 | h1601
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1602 | h1602
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1603 | h1603
                      · linarith only [h1603, hlam, p0_0]
                      · linarith only [h1588, h1601, h1603, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1602, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1607 | h1607
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1608 | h1608
                      · linarith only [h1608, hlam, p0_0]
                      · linarith only [h1588, h1601, h1608, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1607, hlam]
                · linarith only [h1589, hc06, hlam, p0_1]
                · linarith only [h1586, h1589, hc06, hlam, p0_1]
                · linarith only [h1587, h1589, hc06, hlam, p0_1]
                · linarith only [h1588, h1589, hc06, hlam, p0_1]
              · rcases h6emax with h1616 | h1616 | h1616 | h1616 | h1616 | h1616
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1617 | h1617
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1618 | h1618
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1619 | h1619
                      · linarith only [h1619, hlam, p0_0]
                      · linarith only [h1617, h1619, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1618, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1623 | h1623
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1624 | h1624
                      · linarith only [h1624, hlam, p0_0]
                      · linarith only [h1587, h1617, h1624, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h1399, h1623, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1628 | h1628
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1629 | h1629
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1630 | h1630
                      · linarith only [h1630, hlam, p0_0]
                      · linarith only [h1587, h1628, h1630, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1399, h1629, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1634 | h1634
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1635 | h1635
                      · linarith only [h1635, hlam, p0_0]
                      · linarith only [h1587, h1628, h1635, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h1399, h1634, hlam]
                · linarith only [h1616, hc06, hlam, p0_1]
                · linarith only [h1586, h1616, hc06, hlam, p0_1]
                · linarith only [h1587, h1616, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1642 | h1642
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1643 | h1643
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1644 | h1644
                      · linarith only [h1644, hlam, p0_0]
                      · linarith only [h1642, h1644, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1643, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1648 | h1648
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1649 | h1649
                      · linarith only [h1649, hlam, p0_0]
                      · linarith only [h1587, h1642, h1648, h1649, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h1399, h1648, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h1653 | h1653
              · rcases h6emax with h1654 | h1654 | h1654 | h1654 | h1654 | h1654
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1655 | h1655
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1656 | h1656
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1657 | h1657
                      · linarith only [h1657, hlam, p0_0]
                      · linarith only [h1653, h1657, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1656, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1661 | h1661
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1662 | h1662
                      · linarith only [h1662, hlam, p0_0]
                      · linarith only [h1653, h1655, h1662, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1661, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1666 | h1666
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1667 | h1667
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1668 | h1668
                      · linarith only [h1668, hlam, p0_0]
                      · linarith only [h1653, h1668, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1667, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1672 | h1672
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1673 | h1673
                      · linarith only [h1673, hlam, p0_0]
                      · linarith only [h1653, h1666, h1673, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1672, hlam]
                · linarith only [h1654, hc06, hlam, p0_1]
                · linarith only [h1586, h1654, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1679 | h1679
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1680 | h1680
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1681 | h1681
                      · linarith only [h1681, hlam, p0_0]
                      · linarith only [h1653, h1679, h1681, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1680, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1685 | h1685
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1686 | h1686
                      · linarith only [h1686, hlam, p0_0]
                      · linarith only [h1653, h1679, h1686, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1685, hlam]
                · linarith only [h1653, h1654, hc06, hlam, p0_1]
              · rcases h6emax with h1691 | h1691 | h1691 | h1691 | h1691 | h1691
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1692 | h1692
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1693 | h1693
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1694 | h1694
                      · linarith only [h1694, hlam, p0_0]
                      · linarith only [h1692, h1694, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1693, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1698 | h1698
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1699 | h1699
                      · linarith only [h1699, hlam, p0_0]
                      · linarith only [h1586, h1692, h1698, h1699, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h1399, h1698, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1703 | h1703
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1704 | h1704
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1705 | h1705
                      · linarith only [h1705, hlam, p0_0]
                      · linarith only [h1586, h1703, h1705, hc12, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h1399, h1704, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1709 | h1709
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1710 | h1710
                      · linarith only [h1710, hlam, p0_0]
                      · linarith only [h1586, h1703, h1709, h1710, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h1399, h1709, hlam]
                · linarith only [h1691, hc06, hlam, p0_1]
                · linarith only [h1586, h1691, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1716 | h1716
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1717 | h1717
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1718 | h1718
                      · linarith only [h1718, hlam, p0_0]
                      · linarith only [h1718, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1717, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1722 | h1722
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1723 | h1723
                      · linarith only [h1723, hlam, p0_0]
                      · linarith only [h1586, h1716, h1723, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h1399, h1722, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1727 | h1727
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1728 | h1728
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1729 | h1729
                      · linarith only [h1729, hlam, p0_0]
                      · linarith only [h1586, h1727, h1729, hc12, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h1399, h1728, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1733 | h1733
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1734 | h1734
                      · linarith only [h1734, hlam, p0_0]
                      · linarith only [h1586, h1727, h1734, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h1399, h1733, hlam]
          · rcases p0_3 (m.d 4 6) (by simp) with h1738 | h1738
            · rcases p0_3 (m.d 5 6) (by simp) with h1739 | h1739
              · rcases h6emax with h1740 | h1740 | h1740 | h1740 | h1740 | h1740
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1741 | h1741
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1742 | h1742
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1743 | h1743
                      · linarith only [h1743, hlam, p0_0]
                      · linarith only [h1739, h1741, h1743, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1742, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1747 | h1747
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1748 | h1748
                      · linarith only [h1748, hlam, p0_0]
                      · linarith only [h1739, h1741, h1748, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1747, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1752 | h1752
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1753 | h1753
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1754 | h1754
                      · linarith only [h1754, hlam, p0_0]
                      · linarith only [h1739, h1754, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1753, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1758 | h1758
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1759 | h1759
                      · linarith only [h1759, hlam, p0_0]
                      · linarith only [h1739, h1752, h1758, h1759, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h1399, h1758, hlam]
                · linarith only [h1740, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1764 | h1764
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1765 | h1765
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1766 | h1766
                      · linarith only [h1766, hlam, p0_0]
                      · linarith only [h1739, h1766, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1765, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1770 | h1770
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1771 | h1771
                      · linarith only [h1771, hlam, p0_0]
                      · linarith only [h1739, h1764, h1771, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1770, hlam]
                · linarith only [h1738, h1740, hc06, hlam, p0_1]
                · linarith only [h1739, h1740, hc06, hlam, p0_1]
              · rcases h6emax with h1777 | h1777 | h1777 | h1777 | h1777 | h1777
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1778 | h1778
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1779 | h1779
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1780 | h1780
                      · linarith only [h1780, hlam, p0_0]
                      · linarith only [h1778, h1780, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1779, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1784 | h1784
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1785 | h1785
                      · linarith only [h1785, hlam, p0_0]
                      · linarith only [h1738, h1778, h1784, h1785, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h1399, h1784, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1789 | h1789
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1790 | h1790
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1791 | h1791
                      · linarith only [h1791, hlam, p0_0]
                      · linarith only [h1738, h1791, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1399, h1790, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1795 | h1795
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1796 | h1796
                      · linarith only [h1796, hlam, p0_0]
                      · linarith only [h1738, h1789, h1795, h1796, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h1399, h1795, hlam]
                · linarith only [h1777, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1801 | h1801
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1802 | h1802
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1803 | h1803
                      · linarith only [h1803, hlam, p0_0]
                      · linarith only [h1803, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1802, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1807 | h1807
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1808 | h1808
                      · linarith only [h1808, hlam, p0_0]
                      · linarith only [h1738, h1801, h1808, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h1399, h1807, hlam]
                · linarith only [h1738, h1777, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1813 | h1813
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1814 | h1814
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1815 | h1815
                      · linarith only [h1815, hlam, p0_0]
                      · linarith only [h1813, h1815, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1814, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1819 | h1819
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1820 | h1820
                      · linarith only [h1820, hlam, p0_0]
                      · linarith only [h1738, h1813, h1819, h1820, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h1399, h1819, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h1824 | h1824
              · rcases h6emax with h1825 | h1825 | h1825 | h1825 | h1825 | h1825
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1826 | h1826
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1827 | h1827
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1828 | h1828
                      · linarith only [h1828, hlam, p0_0]
                      · linarith only [h1824, h1826, h1828, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1827, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1832 | h1832
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1833 | h1833
                      · linarith only [h1833, hlam, p0_0]
                      · linarith only [h1824, h1826, h1832, h1833, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h1399, h1832, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1837 | h1837
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1838 | h1838
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1839 | h1839
                      · linarith only [h1839, hlam, p0_0]
                      · linarith only [h1824, h1839, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1838, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1843 | h1843
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1844 | h1844
                      · linarith only [h1844, hlam, p0_0]
                      · linarith only [h1824, h1837, h1843, h1844, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h1399, h1843, hlam]
                · linarith only [h1825, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1849 | h1849
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1850 | h1850
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1851 | h1851
                      · linarith only [h1851, hlam, p0_0]
                      · linarith only [h1824, h1851, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1850, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1855 | h1855
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1856 | h1856
                      · linarith only [h1856, hlam, p0_0]
                      · linarith only [h1824, h1849, h1855, h1856, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h1399, h1855, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1860 | h1860
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1861 | h1861
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1862 | h1862
                      · linarith only [h1862, hlam, p0_0]
                      · linarith only [h1824, h1860, h1862, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1861, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1866 | h1866
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1867 | h1867
                      · linarith only [h1867, hlam, p0_0]
                      · linarith only [h1824, h1860, h1867, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h1399, h1866, hlam]
                · linarith only [h1824, h1825, hc06, hlam, p0_1]
              · rcases h6emax with h1872 | h1872 | h1872 | h1872 | h1872 | h1872
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1873 | h1873
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1874 | h1874
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1875 | h1875
                      · linarith only [h1875, hlam, p0_0]
                      · linarith only [h1873, h1875, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1874, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1879 | h1879
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1880 | h1880
                      · linarith only [h1880, hlam, p0_0]
                      · linarith only [h1873, h1880, hc01, hc26, hlam, hphi, ht12, p0_1]
                    · linarith only [h1399, h1879, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1884 | h1884
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1885 | h1885
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1886 | h1886
                      · linarith only [h1886, hlam, p0_0]
                      · linarith only [h1884, h1886, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1885, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1890 | h1890
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1891 | h1891
                      · linarith only [h1891, hlam, p0_0]
                      · linarith only [h1884, h1890, h1891, hc16, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                    · linarith only [h1399, h1890, hlam]
                · linarith only [h1872, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1896 | h1896
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1897 | h1897
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1898 | h1898
                      · linarith only [h1898, hlam, p0_0]
                      · linarith only [h1896, h1898, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1897, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1902 | h1902
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1903 | h1903
                      · linarith only [h1903, hlam, p0_0]
                      · linarith only [h1896, h1903, hc01, hc26, hlam, hphi, ht12, p0_1]
                    · linarith only [h1399, h1902, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1907 | h1907
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1908 | h1908
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1909 | h1909
                      · linarith only [h1909, hlam, p0_0]
                      · linarith only [h1907, h1909, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1908, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1913 | h1913
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1914 | h1914
                      · linarith only [h1914, hlam, p0_0]
                      · linarith only [h1907, h1913, h1914, hc16, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1]
                    · linarith only [h1399, h1913, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1918 | h1918
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1919 | h1919
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1920 | h1920
                      · linarith only [h1920, hlam, p0_0]
                      · linarith only [h1918, h1920, hc12, hc26, hlam, hphi, p0_1]
                    · linarith only [h1399, h1919, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1924 | h1924
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h1925 | h1925
                      · linarith only [h1925, hlam, p0_0]
                      · linarith only [h1918, h1925, hc01, hc26, hlam, hphi, ht12, p0_1]
                    · linarith only [h1399, h1924, hlam]
        · linarith only [h1585, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h1930 | h1930
    · linarith only [h1930, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h1932 | h1932
      · linarith only [h1932, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h1934 | h1934
        · rcases p0_3 (m.d 3 6) (by simp) with h1935 | h1935
          · rcases p0_3 (m.d 4 6) (by simp) with h1936 | h1936
            · rcases p0_3 (m.d 5 6) (by simp) with h1937 | h1937
              · rcases h6emax with h1938 | h1938 | h1938 | h1938 | h1938 | h1938
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1939 | h1939
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1940 | h1940
                    · linarith only [h1930, h1940, hlam]
                    · linarith only [h1939, h1940, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1943 | h1943
                    · linarith only [h1930, h1943, hlam]
                    · linarith only [h1937, h1943, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1946 | h1946
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1947 | h1947
                    · linarith only [h1930, h1947, hlam]
                    · linarith only [h1937, h1947, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1950 | h1950
                    · linarith only [h1930, h1950, hlam]
                    · linarith only [h1937, h1950, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h1938, hc16, hlam, p0_1]
                · linarith only [h1935, h1938, hc16, hlam, p0_1]
                · linarith only [h1936, h1938, hc16, hlam, p0_1]
                · linarith only [h1937, h1938, hc16, hlam, p0_1]
              · rcases h6emax with h1957 | h1957 | h1957 | h1957 | h1957 | h1957
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1958 | h1958
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1959 | h1959
                    · linarith only [h1930, h1959, hlam]
                    · linarith only [h1958, h1959, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1962 | h1962
                    · linarith only [h1930, h1962, hlam]
                    · linarith only [h1936, h1962, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1965 | h1965
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1966 | h1966
                    · linarith only [h1930, h1966, hlam]
                    · linarith only [h1936, h1966, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1969 | h1969
                    · linarith only [h1930, h1969, hlam]
                    · linarith only [h1936, h1969, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h1957, hc16, hlam, p0_1]
                · linarith only [h1935, h1957, hc16, hlam, p0_1]
                · linarith only [h1936, h1957, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1975 | h1975
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1976 | h1976
                    · linarith only [h1930, h1976, hlam]
                    · linarith only [h1975, h1976, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1979 | h1979
                    · linarith only [h1930, h1979, hlam]
                    · linarith only [h1936, h1979, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h1982 | h1982
              · rcases h6emax with h1983 | h1983 | h1983 | h1983 | h1983 | h1983
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1984 | h1984
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1985 | h1985
                    · linarith only [h1930, h1985, hlam]
                    · linarith only [h1982, h1984, h1985, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1988 | h1988
                    · linarith only [h1930, h1988, hlam]
                    · linarith only [h1982, h1988, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h1991 | h1991
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1992 | h1992
                    · linarith only [h1930, h1992, hlam]
                    · linarith only [h1982, h1992, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h1995 | h1995
                    · linarith only [h1930, h1995, hlam]
                    · linarith only [h1982, h1995, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h1983, hc16, hlam, p0_1]
                · linarith only [h1935, h1983, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2000 | h2000
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2001 | h2001
                    · linarith only [h1930, h2001, hlam]
                    · linarith only [h1982, h2000, h2001, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2004 | h2004
                    · linarith only [h1930, h2004, hlam]
                    · linarith only [h1982, h2004, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h1982, h1983, hc16, hlam, p0_1]
              · rcases h6emax with h2008 | h2008 | h2008 | h2008 | h2008 | h2008
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2009 | h2009
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2010 | h2010
                    · linarith only [h1930, h2010, hlam]
                    · linarith only [h2009, h2010, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2013 | h2013
                    · linarith only [h1930, h2013, hlam]
                    · linarith only [h1935, h2013, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2016 | h2016
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2017 | h2017
                    · linarith only [h1930, h2017, hlam]
                    · linarith only [h1935, h2016, h2017, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2020 | h2020
                    · linarith only [h1930, h2020, hlam]
                    · linarith only [h1935, h2020, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h2008, hc16, hlam, p0_1]
                · linarith only [h1935, h2008, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2025 | h2025
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2026 | h2026
                    · linarith only [h1930, h2026, hlam]
                    · linarith only [h2025, h2026, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2029 | h2029
                    · linarith only [h1930, h2029, hlam]
                    · linarith only [h1935, h2029, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2032 | h2032
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2033 | h2033
                    · linarith only [h1930, h2033, hlam]
                    · linarith only [h1935, h2032, h2033, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2036 | h2036
                    · linarith only [h1930, h2036, hlam]
                    · linarith only [h1935, h2036, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h2039 | h2039
            · rcases p0_3 (m.d 5 6) (by simp) with h2040 | h2040
              · rcases h6emax with h2041 | h2041 | h2041 | h2041 | h2041 | h2041
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2042 | h2042
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2043 | h2043
                    · linarith only [h1930, h2043, hlam]
                    · linarith only [h2040, h2043, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2046 | h2046
                    · linarith only [h1930, h2046, hlam]
                    · linarith only [h2040, h2046, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2049 | h2049
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2050 | h2050
                    · linarith only [h1930, h2050, hlam]
                    · linarith only [h2040, h2050, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2053 | h2053
                    · linarith only [h1930, h2053, hlam]
                    · linarith only [h2040, h2053, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2041, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2057 | h2057
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2058 | h2058
                    · linarith only [h1930, h2058, hlam]
                    · linarith only [h2040, h2058, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2061 | h2061
                    · linarith only [h1930, h2061, hlam]
                    · linarith only [h2040, h2061, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2039, h2041, hc16, hlam, p0_1]
                · linarith only [h2040, h2041, hc16, hlam, p0_1]
              · rcases h6emax with h2066 | h2066 | h2066 | h2066 | h2066 | h2066
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2067 | h2067
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2068 | h2068
                    · linarith only [h1930, h2068, hlam]
                    · linarith only [h2067, h2068, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2071 | h2071
                    · linarith only [h1930, h2071, hlam]
                    · linarith only [h2039, h2071, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2074 | h2074
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2075 | h2075
                    · linarith only [h1930, h2075, hlam]
                    · linarith only [h2039, h2074, h2075, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2078 | h2078
                    · linarith only [h1930, h2078, hlam]
                    · linarith only [h2039, h2078, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h2066, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2082 | h2082
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2083 | h2083
                    · linarith only [h1930, h2083, hlam]
                    · linarith only [h2082, h2083, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2086 | h2086
                    · linarith only [h1930, h2086, hlam]
                    · linarith only [h2039, h2086, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h2039, h2066, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2090 | h2090
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2091 | h2091
                    · linarith only [h1930, h2091, hlam]
                    · linarith only [h2090, h2091, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2094 | h2094
                    · linarith only [h1930, h2094, hlam]
                    · linarith only [h2039, h2094, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h2097 | h2097
              · rcases h6emax with h2098 | h2098 | h2098 | h2098 | h2098 | h2098
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2099 | h2099
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2100 | h2100
                    · linarith only [h1930, h2100, hlam]
                    · linarith only [h2097, h2099, h2100, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2103 | h2103
                    · linarith only [h1930, h2103, hlam]
                    · linarith only [h2097, h2103, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2106 | h2106
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2107 | h2107
                    · linarith only [h1930, h2107, hlam]
                    · linarith only [h2097, h2106, h2107, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2110 | h2110
                    · linarith only [h1930, h2110, hlam]
                    · linarith only [h2097, h2110, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2098, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2114 | h2114
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2115 | h2115
                    · linarith only [h1930, h2115, hlam]
                    · linarith only [h2097, h2114, h2115, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2118 | h2118
                    · linarith only [h1930, h2118, hlam]
                    · linarith only [h2097, h2118, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2121 | h2121
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2122 | h2122
                    · linarith only [h1930, h2122, hlam]
                    · linarith only [h2097, h2121, h2122, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2125 | h2125
                    · linarith only [h1930, h2125, hlam]
                    · linarith only [h2097, h2125, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2097, h2098, hc16, hlam, p0_1]
              · rcases h6emax with h2129 | h2129 | h2129 | h2129 | h2129 | h2129
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2130 | h2130
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2131 | h2131
                    · linarith only [h1930, h2131, hlam]
                    · linarith only [h2130, h2131, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2134 | h2134
                    · linarith only [h1930, h2134, hlam]
                    · linarith only [h2134, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2137 | h2137
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2138 | h2138
                    · linarith only [h1930, h2138, hlam]
                    · linarith only [h2137, h2138, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2141 | h2141
                    · linarith only [h1930, h2141, hlam]
                    · linarith only [h2141, hc01, hc26, hlam, hphi, ht12, p0_1]
                · linarith only [h2129, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2145 | h2145
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2146 | h2146
                    · linarith only [h1930, h2146, hlam]
                    · linarith only [h2145, h2146, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2149 | h2149
                    · linarith only [h1930, h2149, hlam]
                    · linarith only [h2149, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2152 | h2152
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2153 | h2153
                    · linarith only [h1930, h2153, hlam]
                    · linarith only [h2152, h2153, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2156 | h2156
                    · linarith only [h1930, h2156, hlam]
                    · linarith only [h2156, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2159 | h2159
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2160 | h2160
                    · linarith only [h1930, h2160, hlam]
                    · linarith only [h2160, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2163 | h2163
                    · linarith only [h1930, h2163, hlam]
                    · linarith only [h2163, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h1934, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2168 | h2168
    · linarith only [h2168, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h2170 | h2170
      · rcases p0_3 (m.d 2 6) (by simp) with h2171 | h2171
        · rcases p0_3 (m.d 3 6) (by simp) with h2172 | h2172
          · linarith only [h2172, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2174 | h2174
            · rcases p0_3 (m.d 5 6) (by simp) with h2175 | h2175
              · rcases h6emax with h2176 | h2176 | h2176 | h2176 | h2176 | h2176
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2177 | h2177
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2178 | h2178
                    · linarith only [h2170, h2178, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2178, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2181 | h2181
                    · linarith only [h2168, h2170, h2181, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2181, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2168, h2170, h2176, hc06, hlam, p0_1]
                · linarith only [h2168, h2176, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2186 | h2186
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2187 | h2187
                    · linarith only [h2168, h2170, h2187, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2186, h2187, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2190 | h2190
                    · linarith only [h2168, h2170, h2190, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2190, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2168, h2174, h2176, hc06, hlam, p0_1]
                · linarith only [h2168, h2175, h2176, hc06, hlam, p0_1]
              · rcases h6emax with h2195 | h2195 | h2195 | h2195 | h2195 | h2195
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2196 | h2196
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2197 | h2197
                    · linarith only [h2168, h2170, h2197, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2197, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2200 | h2200
                    · linarith only [h2168, h2170, h2196, h2200, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2200, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2168, h2170, h2195, hc06, hlam, p0_1]
                · linarith only [h2168, h2195, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2205 | h2205
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2206 | h2206
                    · linarith only [h2168, h2170, h2206, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2206, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2209 | h2209
                    · linarith only [h2168, h2170, h2205, h2209, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2209, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2168, h2174, h2195, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2213 | h2213
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2214 | h2214
                    · linarith only [h2168, h2170, h2214, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2213, h2214, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2217 | h2217
                    · linarith only [h2168, h2170, h2217, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2217, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h2220 | h2220
              · rcases h6emax with h2221 | h2221 | h2221 | h2221 | h2221 | h2221
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2222 | h2222
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2223 | h2223
                    · linarith only [h2168, h2170, h2223, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2223, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2226 | h2226
                    · linarith only [h2168, h2170, h2222, h2226, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2226, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2168, h2170, h2221, hc06, hlam, p0_1]
                · linarith only [h2168, h2221, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2231 | h2231
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2232 | h2232
                    · linarith only [h2168, h2170, h2232, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2232, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2235 | h2235
                    · linarith only [h2168, h2170, h2231, h2235, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2235, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2238 | h2238
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2239 | h2239
                    · linarith only [h2168, h2170, h2239, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2239, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2242 | h2242
                    · linarith only [h2168, h2170, h2238, h2242, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2242, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2168, h2220, h2221, hc06, hlam, p0_1]
              · rcases h6emax with h2246 | h2246 | h2246 | h2246 | h2246 | h2246
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2247 | h2247
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2248 | h2248
                    · linarith only [h2168, h2170, h2248, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2246, h2247, h2248, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2251 | h2251
                    · linarith only [h2168, h2170, h2247, h2251, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2251, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2168, h2170, h2246, hc06, hlam, p0_1]
                · linarith only [h2168, h2246, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2256 | h2256
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2257 | h2257
                    · linarith only [h2168, h2170, h2257, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2257, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2260 | h2260
                    · linarith only [h2168, h2170, h2256, h2260, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2260, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2263 | h2263
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2264 | h2264
                    · linarith only [h2168, h2170, h2264, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2263, h2264, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2267 | h2267
                    · linarith only [h2168, h2170, h2263, h2267, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2267, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2270 | h2270
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2271 | h2271
                    · linarith only [h2168, h2170, h2271, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2168, h2170, h2271, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2274 | h2274
                    · linarith only [h2168, h2170, h2270, h2274, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2168, h2170, h2274, hc01, hc16, hlam, hphi, p0_1]
        · linarith only [h2171, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2278 | h2278
        · rcases p0_3 (m.d 3 6) (by simp) with h2279 | h2279
          · linarith only [h2279, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h2281 | h2281
            · rcases p0_3 (m.d 5 6) (by simp) with h2282 | h2282
              · rcases h6emax with h2283 | h2283 | h2283 | h2283 | h2283 | h2283
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2284 | h2284
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2285 | h2285
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2286 | h2286
                      · linarith only [h2168, h2284, h2285, h2286, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h2168, h2282, h2286, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2282, h2285, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2290 | h2290
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2291 | h2291
                      · linarith only [h2168, h2290, h2291, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2282, h2291, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2282, h2290, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2295 | h2295
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2296 | h2296
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2297 | h2297
                      · linarith only [h2168, h2297, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2297, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2283, h2296, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2301 | h2301
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2302 | h2302
                      · linarith only [h2168, h2301, h2302, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2282, h2302, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2283, h2301, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2168, h2283, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2307 | h2307
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2308 | h2308
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2309 | h2309
                      · linarith only [h2168, h2308, h2309, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2282, h2309, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2282, h2308, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2313 | h2313
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2314 | h2314
                      · linarith only [h2168, h2313, h2314, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2282, h2314, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2282, h2313, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2168, h2281, h2283, hc06, hlam, p0_1]
                · linarith only [h2168, h2282, h2283, hc06, hlam, p0_1]
              · rcases h6emax with h2320 | h2320 | h2320 | h2320 | h2320 | h2320
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2321 | h2321
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2322 | h2322
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2323 | h2323
                      · linarith only [h2168, h2322, h2323, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2323, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2281, h2322, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2327 | h2327
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2328 | h2328
                      · linarith only [h2168, h2328, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2328, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2281, h2327, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2332 | h2332
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2333 | h2333
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2334 | h2334
                      · linarith only [h2168, h2334, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2334, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2320, h2333, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2338 | h2338
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2339 | h2339
                      · linarith only [h2168, h2339, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2339, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2320, h2338, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2168, h2320, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2344 | h2344
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2345 | h2345
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2346 | h2346
                      · linarith only [h2168, h2345, h2346, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2346, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2281, h2345, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2350 | h2350
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2351 | h2351
                      · linarith only [h2168, h2351, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2351, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2281, h2350, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h2168, h2281, h2320, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2356 | h2356
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2357 | h2357
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2358 | h2358
                      · linarith only [h2168, h2357, h2358, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2358, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2281, h2357, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2362 | h2362
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2363 | h2363
                      · linarith only [h2168, h2363, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2363, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2281, h2362, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h2367 | h2367
              · rcases h6emax with h2368 | h2368 | h2368 | h2368 | h2368 | h2368
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2369 | h2369
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2370 | h2370
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2371 | h2371
                      · linarith only [h2168, h2370, h2371, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2367, h2371, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2367, h2370, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2375 | h2375
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2376 | h2376
                      · linarith only [h2168, h2375, h2376, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2367, h2376, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2367, h2375, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2380 | h2380
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2381 | h2381
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2382 | h2382
                      · linarith only [h2168, h2382, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2382, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2367, h2381, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2386 | h2386
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2387 | h2387
                      · linarith only [h2168, h2386, h2387, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2367, h2387, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2368, h2386, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2168, h2368, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2392 | h2392
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2393 | h2393
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2394 | h2394
                      · linarith only [h2168, h2393, h2394, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2367, h2394, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2367, h2393, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2398 | h2398
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2399 | h2399
                      · linarith only [h2168, h2398, h2399, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2367, h2399, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2367, h2398, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2403 | h2403
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2404 | h2404
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2405 | h2405
                      · linarith only [h2168, h2405, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2367, h2405, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2367, h2403, h2404, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2409 | h2409
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2410 | h2410
                      · linarith only [h2168, h2409, h2410, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2367, h2410, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2170, h2367, h2409, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2168, h2367, h2368, hc06, hlam, p0_1]
              · rcases h6emax with h2415 | h2415 | h2415 | h2415 | h2415 | h2415
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2416 | h2416
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2417 | h2417
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2418 | h2418
                      · linarith only [h2168, h2418, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2418, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2417, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2422 | h2422
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2423 | h2423
                      · linarith only [h2168, h2423, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2423, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2422, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2427 | h2427
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2428 | h2428
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2429 | h2429
                      · linarith only [h2168, h2429, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2429, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2415, h2428, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2433 | h2433
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2434 | h2434
                      · linarith only [h2168, h2434, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2434, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2415, h2433, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2168, h2415, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2439 | h2439
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2440 | h2440
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2441 | h2441
                      · linarith only [h2168, h2440, h2441, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2441, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2440, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2445 | h2445
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2446 | h2446
                      · linarith only [h2168, h2446, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2446, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2445, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2450 | h2450
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2451 | h2451
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2452 | h2452
                      · linarith only [h2168, h2452, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2452, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2451, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2456 | h2456
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2457 | h2457
                      · linarith only [h2168, h2457, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2457, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2456, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2461 | h2461
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2462 | h2462
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2463 | h2463
                      · linarith only [h2168, h2463, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2463, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2462, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2467 | h2467
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2468 | h2468
                      · linarith only [h2168, h2468, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2168, h2468, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2170, h2467, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h2278, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2473 | h2473
    · linarith only [h2473, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h2475 | h2475
      · rcases p0_3 (m.d 2 6) (by simp) with h2476 | h2476
        · rcases p0_3 (m.d 3 6) (by simp) with h2477 | h2477
          · rcases p0_3 (m.d 4 6) (by simp) with h2478 | h2478
            · linarith only [h2478, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2480 | h2480
              · rcases h6emax with h2481 | h2481 | h2481 | h2481 | h2481 | h2481
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2482 | h2482
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2483 | h2483
                    · linarith only [h2475, h2483, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2481, h2482, h2483, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2486 | h2486
                    · linarith only [h2473, h2475, h2486, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2486, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2473, h2475, h2481, hc06, hlam, p0_1]
                · linarith only [h2473, h2481, hc06, hlam, p0_1]
                · linarith only [h2473, h2477, h2481, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2492 | h2492
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2493 | h2493
                    · linarith only [h2473, h2475, h2493, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2493, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2496 | h2496
                    · linarith only [h2473, h2475, h2492, h2496, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2496, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2473, h2480, h2481, hc06, hlam, p0_1]
              · rcases h6emax with h2500 | h2500 | h2500 | h2500 | h2500 | h2500
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2501 | h2501
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2502 | h2502
                    · linarith only [h2473, h2475, h2502, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2502, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2505 | h2505
                    · linarith only [h2473, h2475, h2501, h2505, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2505, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2473, h2475, h2500, hc06, hlam, p0_1]
                · linarith only [h2473, h2500, hc06, hlam, p0_1]
                · linarith only [h2473, h2477, h2500, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2511 | h2511
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2512 | h2512
                    · linarith only [h2473, h2475, h2512, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2512, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2515 | h2515
                    · linarith only [h2473, h2475, h2511, h2515, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2515, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2518 | h2518
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2519 | h2519
                    · linarith only [h2473, h2475, h2519, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2519, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2522 | h2522
                    · linarith only [h2473, h2475, h2518, h2522, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2522, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h2525 | h2525
            · linarith only [h2525, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2527 | h2527
              · rcases h6emax with h2528 | h2528 | h2528 | h2528 | h2528 | h2528
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2529 | h2529
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2530 | h2530
                    · linarith only [h2473, h2475, h2530, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2530, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2533 | h2533
                    · linarith only [h2473, h2475, h2529, h2533, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2533, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2473, h2475, h2528, hc06, hlam, p0_1]
                · linarith only [h2473, h2528, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2538 | h2538
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2539 | h2539
                    · linarith only [h2473, h2475, h2539, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2539, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2542 | h2542
                    · linarith only [h2473, h2475, h2538, h2542, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2542, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2545 | h2545
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2546 | h2546
                    · linarith only [h2473, h2475, h2546, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2546, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2549 | h2549
                    · linarith only [h2473, h2475, h2545, h2549, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2549, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2473, h2527, h2528, hc06, hlam, p0_1]
              · rcases h6emax with h2553 | h2553 | h2553 | h2553 | h2553 | h2553
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2554 | h2554
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2555 | h2555
                    · linarith only [h2473, h2475, h2555, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2553, h2554, h2555, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2558 | h2558
                    · linarith only [h2473, h2475, h2554, h2558, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2558, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2473, h2475, h2553, hc06, hlam, p0_1]
                · linarith only [h2473, h2553, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2563 | h2563
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2564 | h2564
                    · linarith only [h2473, h2475, h2564, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2564, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2567 | h2567
                    · linarith only [h2473, h2475, h2563, h2567, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2473, h2475, h2567, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2570 | h2570
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2571 | h2571
                    · linarith only [h2473, h2475, h2571, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2571, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2574 | h2574
                    · linarith only [h2473, h2475, h2574, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2574, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2577 | h2577
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2578 | h2578
                    · linarith only [h2473, h2475, h2578, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2578, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2581 | h2581
                    · linarith only [h2473, h2475, h2581, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2473, h2475, h2581, hc01, hc16, hlam, hphi, p0_1]
        · linarith only [h2476, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2585 | h2585
        · rcases p0_3 (m.d 3 6) (by simp) with h2586 | h2586
          · rcases p0_3 (m.d 4 6) (by simp) with h2587 | h2587
            · linarith only [h2587, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2589 | h2589
              · rcases h6emax with h2590 | h2590 | h2590 | h2590 | h2590 | h2590
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2591 | h2591
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2592 | h2592
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2593 | h2593
                      · linarith only [h2473, h2591, h2592, h2593, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h2473, h2589, h2593, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2589, h2591, h2592, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2597 | h2597
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2598 | h2598
                      · linarith only [h2473, h2597, h2598, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2589, h2598, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2589, h2597, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2602 | h2602
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2603 | h2603
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2604 | h2604
                      · linarith only [h2473, h2604, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2604, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2590, h2603, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2608 | h2608
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2609 | h2609
                      · linarith only [h2473, h2608, h2609, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2589, h2609, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2590, h2608, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2473, h2590, hc06, hlam, p0_1]
                · linarith only [h2473, h2586, h2590, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2615 | h2615
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2616 | h2616
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2617 | h2617
                      · linarith only [h2473, h2616, h2617, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2589, h2617, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2589, h2616, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2621 | h2621
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2622 | h2622
                      · linarith only [h2473, h2621, h2622, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2589, h2622, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2589, h2621, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2473, h2589, h2590, hc06, hlam, p0_1]
              · rcases h6emax with h2627 | h2627 | h2627 | h2627 | h2627 | h2627
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2628 | h2628
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2629 | h2629
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2630 | h2630
                      · linarith only [h2473, h2629, h2630, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2630, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2586, h2629, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2634 | h2634
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2635 | h2635
                      · linarith only [h2473, h2635, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2635, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2586, h2634, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2639 | h2639
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2640 | h2640
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2641 | h2641
                      · linarith only [h2473, h2641, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2641, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2627, h2640, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2645 | h2645
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2646 | h2646
                      · linarith only [h2473, h2646, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2646, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2627, h2645, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2473, h2627, hc06, hlam, p0_1]
                · linarith only [h2473, h2586, h2627, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2652 | h2652
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2653 | h2653
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2654 | h2654
                      · linarith only [h2473, h2653, h2654, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2654, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2586, h2652, h2653, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2658 | h2658
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2659 | h2659
                      · linarith only [h2473, h2659, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2659, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2586, h2658, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2663 | h2663
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2664 | h2664
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2665 | h2665
                      · linarith only [h2473, h2665, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2665, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2586, h2664, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2669 | h2669
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2670 | h2670
                      · linarith only [h2473, h2670, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2670, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2586, h2669, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h2674 | h2674
            · linarith only [h2674, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h2676 | h2676
              · rcases h6emax with h2677 | h2677 | h2677 | h2677 | h2677 | h2677
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2678 | h2678
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2679 | h2679
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2680 | h2680
                      · linarith only [h2473, h2679, h2680, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2680, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2676, h2679, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2684 | h2684
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2685 | h2685
                      · linarith only [h2473, h2684, h2685, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2685, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2676, h2684, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2689 | h2689
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2690 | h2690
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2691 | h2691
                      · linarith only [h2473, h2691, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2691, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2677, h2689, h2690, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2695 | h2695
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2696 | h2696
                      · linarith only [h2473, h2695, h2696, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2696, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2677, h2695, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2473, h2677, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2701 | h2701
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2702 | h2702
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2703 | h2703
                      · linarith only [h2473, h2702, h2703, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2703, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2676, h2701, h2702, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2707 | h2707
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2708 | h2708
                      · linarith only [h2473, h2707, h2708, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2708, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2676, h2707, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2712 | h2712
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2713 | h2713
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2714 | h2714
                      · linarith only [h2473, h2714, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2714, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2676, h2713, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2718 | h2718
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2719 | h2719
                      · linarith only [h2473, h2718, h2719, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2676, h2719, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h2475, h2676, h2718, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h2473, h2676, h2677, hc06, hlam, p0_1]
              · rcases h6emax with h2724 | h2724 | h2724 | h2724 | h2724 | h2724
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2725 | h2725
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2726 | h2726
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2727 | h2727
                      · linarith only [h2473, h2726, h2727, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2727, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2726, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2731 | h2731
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2732 | h2732
                      · linarith only [h2473, h2732, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2732, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2731, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2736 | h2736
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2737 | h2737
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2738 | h2738
                      · linarith only [h2473, h2738, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2738, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2724, h2737, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2742 | h2742
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2743 | h2743
                      · linarith only [h2473, h2743, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2743, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2724, h2742, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2473, h2724, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2748 | h2748
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2749 | h2749
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2750 | h2750
                      · linarith only [h2473, h2749, h2750, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2750, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2749, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2754 | h2754
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2755 | h2755
                      · linarith only [h2473, h2755, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2755, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2754, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2759 | h2759
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2760 | h2760
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2761 | h2761
                      · linarith only [h2473, h2761, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2761, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2760, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2765 | h2765
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2766 | h2766
                      · linarith only [h2473, h2766, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2766, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2765, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2770 | h2770
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2771 | h2771
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2772 | h2772
                      · linarith only [h2473, h2772, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2772, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2770, h2771, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2776 | h2776
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2777 | h2777
                      · linarith only [h2473, h2777, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2473, h2777, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2475, h2776, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h2585, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h2782 | h2782
    · linarith only [h2782, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h2784 | h2784
      · rcases p0_3 (m.d 2 6) (by simp) with h2785 | h2785
        · rcases p0_3 (m.d 3 6) (by simp) with h2786 | h2786
          · rcases p0_3 (m.d 4 6) (by simp) with h2787 | h2787
            · rcases p0_3 (m.d 5 6) (by simp) with h2788 | h2788
              · linarith only [h2788, hlam, p0_0]
              · rcases h6emax with h2790 | h2790 | h2790 | h2790 | h2790 | h2790
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2791 | h2791
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2792 | h2792
                    · linarith only [h2784, h2792, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2792, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2795 | h2795
                    · linarith only [h2782, h2784, h2791, h2795, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2795, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2782, h2784, h2790, hc06, hlam, p0_1]
                · linarith only [h2782, h2790, hc06, hlam, p0_1]
                · linarith only [h2782, h2786, h2790, hc06, hlam, p0_1]
                · linarith only [h2782, h2787, h2790, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2802 | h2802
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2803 | h2803
                    · linarith only [h2782, h2784, h2803, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2802, h2803, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2806 | h2806
                    · linarith only [h2782, h2784, h2806, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2806, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h2809 | h2809
              · linarith only [h2809, hlam, p0_0]
              · rcases h6emax with h2811 | h2811 | h2811 | h2811 | h2811 | h2811
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2812 | h2812
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2813 | h2813
                    · linarith only [h2782, h2784, h2813, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2813, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2816 | h2816
                    · linarith only [h2782, h2784, h2812, h2816, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2816, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2782, h2784, h2811, hc06, hlam, p0_1]
                · linarith only [h2782, h2811, hc06, hlam, p0_1]
                · linarith only [h2782, h2786, h2811, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2822 | h2822
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2823 | h2823
                    · linarith only [h2782, h2784, h2823, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2823, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2826 | h2826
                    · linarith only [h2782, h2784, h2822, h2826, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2826, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2829 | h2829
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2830 | h2830
                    · linarith only [h2782, h2784, h2830, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2829, h2830, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2833 | h2833
                    · linarith only [h2782, h2784, h2833, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2833, hc01, hc16, hlam, hphi, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h2836 | h2836
            · rcases p0_3 (m.d 5 6) (by simp) with h2837 | h2837
              · linarith only [h2837, hlam, p0_0]
              · rcases h6emax with h2839 | h2839 | h2839 | h2839 | h2839 | h2839
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2840 | h2840
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2841 | h2841
                    · linarith only [h2782, h2784, h2841, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2839, h2840, h2841, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2844 | h2844
                    · linarith only [h2782, h2784, h2840, h2844, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2844, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2782, h2784, h2839, hc06, hlam, p0_1]
                · linarith only [h2782, h2839, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2849 | h2849
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2850 | h2850
                    · linarith only [h2782, h2784, h2850, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2850, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2853 | h2853
                    · linarith only [h2782, h2784, h2849, h2853, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2853, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2782, h2836, h2839, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2857 | h2857
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2858 | h2858
                    · linarith only [h2782, h2784, h2858, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2857, h2858, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2861 | h2861
                    · linarith only [h2782, h2784, h2861, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2861, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h2864 | h2864
              · linarith only [h2864, hlam, p0_0]
              · rcases h6emax with h2866 | h2866 | h2866 | h2866 | h2866 | h2866
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2867 | h2867
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2868 | h2868
                    · linarith only [h2782, h2784, h2868, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2866, h2867, h2868, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2871 | h2871
                    · linarith only [h2782, h2784, h2867, h2871, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2871, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h2782, h2784, h2866, hc06, hlam, p0_1]
                · linarith only [h2782, h2866, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2876 | h2876
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2877 | h2877
                    · linarith only [h2782, h2784, h2877, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2877, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2880 | h2880
                    · linarith only [h2782, h2784, h2876, h2880, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2880, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2883 | h2883
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2884 | h2884
                    · linarith only [h2782, h2784, h2884, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2884, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2887 | h2887
                    · linarith only [h2782, h2784, h2883, h2887, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2887, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2890 | h2890
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2891 | h2891
                    · linarith only [h2782, h2784, h2891, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h2782, h2784, h2891, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2894 | h2894
                    · linarith only [h2782, h2784, h2890, h2894, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h2782, h2784, h2894, hc01, hc16, hlam, hphi, p0_1]
        · linarith only [h2785, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h2898 | h2898
        · rcases p0_3 (m.d 3 6) (by simp) with h2899 | h2899
          · rcases p0_3 (m.d 4 6) (by simp) with h2900 | h2900
            · rcases p0_3 (m.d 5 6) (by simp) with h2901 | h2901
              · linarith only [h2901, hlam, p0_0]
              · rcases h6emax with h2903 | h2903 | h2903 | h2903 | h2903 | h2903
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2904 | h2904
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2905 | h2905
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2906 | h2906
                      · linarith only [h2782, h2904, h2906, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h2782, h2906, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2900, h2905, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2910 | h2910
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2911 | h2911
                      · linarith only [h2782, h2911, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2911, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2900, h2910, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2915 | h2915
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2916 | h2916
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2917 | h2917
                      · linarith only [h2782, h2917, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2917, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2903, h2915, h2916, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2921 | h2921
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2922 | h2922
                      · linarith only [h2782, h2922, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2922, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2903, h2921, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2782, h2903, hc06, hlam, p0_1]
                · linarith only [h2782, h2899, h2903, hc06, hlam, p0_1]
                · linarith only [h2782, h2900, h2903, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2929 | h2929
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2930 | h2930
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2931 | h2931
                      · linarith only [h2782, h2930, h2931, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2931, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2900, h2930, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2935 | h2935
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2936 | h2936
                      · linarith only [h2782, h2936, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2936, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2900, h2935, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h2940 | h2940
              · linarith only [h2940, hlam, p0_0]
              · rcases h6emax with h2942 | h2942 | h2942 | h2942 | h2942 | h2942
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2943 | h2943
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2944 | h2944
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2945 | h2945
                      · linarith only [h2782, h2945, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2945, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2899, h2944, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2949 | h2949
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2950 | h2950
                      · linarith only [h2782, h2950, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2950, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2899, h2949, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2954 | h2954
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2955 | h2955
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2956 | h2956
                      · linarith only [h2782, h2956, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2956, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2942, h2954, h2955, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2960 | h2960
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2961 | h2961
                      · linarith only [h2782, h2961, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2961, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2942, h2960, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2782, h2942, hc06, hlam, p0_1]
                · linarith only [h2782, h2899, h2942, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2967 | h2967
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2968 | h2968
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2969 | h2969
                      · linarith only [h2782, h2968, h2969, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2969, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2899, h2968, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2973 | h2973
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2974 | h2974
                      · linarith only [h2782, h2974, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2974, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2899, h2973, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2978 | h2978
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2979 | h2979
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2980 | h2980
                      · linarith only [h2782, h2980, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2980, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2899, h2979, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2984 | h2984
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2985 | h2985
                      · linarith only [h2782, h2985, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2985, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2899, h2984, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 6) (by simp) with h2989 | h2989
            · rcases p0_3 (m.d 5 6) (by simp) with h2990 | h2990
              · linarith only [h2990, hlam, p0_0]
              · rcases h6emax with h2992 | h2992 | h2992 | h2992 | h2992 | h2992
                · rcases m.htr 0 1 2 (by decide) (by decide) with h2993 | h2993
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2994 | h2994
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h2995 | h2995
                      · linarith only [h2782, h2995, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h2995, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2989, h2993, h2994, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h2999 | h2999
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3000 | h3000
                      · linarith only [h2782, h3000, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3000, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2989, h2999, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3004 | h3004
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3005 | h3005
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3006 | h3006
                      · linarith only [h2782, h3006, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3006, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2992, h3004, h3005, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3010 | h3010
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3011 | h3011
                      · linarith only [h2782, h3011, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3011, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2992, h3010, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2782, h2992, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3016 | h3016
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3017 | h3017
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3018 | h3018
                      · linarith only [h2782, h3017, h3018, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3018, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2989, h3017, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3022 | h3022
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3023 | h3023
                      · linarith only [h2782, h3023, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3023, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2989, h3022, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h2782, h2989, h2992, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3028 | h3028
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3029 | h3029
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3030 | h3030
                      · linarith only [h2782, h3029, h3030, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3030, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2989, h3029, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3034 | h3034
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3035 | h3035
                      · linarith only [h2782, h3035, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3035, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h2989, h3034, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h3039 | h3039
              · linarith only [h3039, hlam, p0_0]
              · rcases h6emax with h3041 | h3041 | h3041 | h3041 | h3041 | h3041
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3042 | h3042
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3043 | h3043
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3044 | h3044
                      · linarith only [h2782, h3044, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3044, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3043, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3048 | h3048
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3049 | h3049
                      · linarith only [h2782, h3049, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3049, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3048, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3053 | h3053
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3054 | h3054
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3055 | h3055
                      · linarith only [h2782, h3055, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3055, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3041, h3053, h3054, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3059 | h3059
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3060 | h3060
                      · linarith only [h2782, h3060, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3060, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3041, h3059, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h2782, h3041, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3065 | h3065
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3066 | h3066
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3067 | h3067
                      · linarith only [h2782, h3066, h3067, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3067, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3065, h3066, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3071 | h3071
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3072 | h3072
                      · linarith only [h2782, h3072, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3072, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3071, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3076 | h3076
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3077 | h3077
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3078 | h3078
                      · linarith only [h2782, h3078, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3078, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3077, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3082 | h3082
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3083 | h3083
                      · linarith only [h2782, h3083, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3083, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3082, hc01, hc26, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3087 | h3087
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3088 | h3088
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3089 | h3089
                      · linarith only [h2782, h3089, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3089, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3088, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3093 | h3093
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3094 | h3094
                      · linarith only [h2782, h3094, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h2782, h3094, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h2784, h3093, hc01, hc26, hlam, hphi, ht12, p0_1]
        · linarith only [h2898, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h3099 | h3099
    · linarith only [h3099, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h3101 | h3101
      · rcases p0_3 (m.d 2 6) (by simp) with h3102 | h3102
        · rcases p0_3 (m.d 3 6) (by simp) with h3103 | h3103
          · rcases p0_3 (m.d 4 6) (by simp) with h3104 | h3104
            · rcases p0_3 (m.d 5 6) (by simp) with h3105 | h3105
              · rcases h6emax with h3106 | h3106 | h3106 | h3106 | h3106 | h3106
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3107 | h3107
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3108 | h3108
                    · linarith only [h3101, h3108, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3106, h3107, h3108, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3111 | h3111
                    · linarith only [h3101, h3107, h3111, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3111, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3106, hc06, hlam, p0_1]
                · linarith only [h3102, h3106, hc06, hlam, p0_1]
                · linarith only [h3106, hc06, hlam, p0_1]
                · linarith only [h3104, h3106, hc06, hlam, p0_1]
                · linarith only [h3105, h3106, hc06, hlam, p0_1]
              · rcases h6emax with h3119 | h3119 | h3119 | h3119 | h3119 | h3119
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3120 | h3120
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3121 | h3121
                    · linarith only [h3101, h3121, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3119, h3120, h3121, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3124 | h3124
                    · linarith only [h3101, h3124, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3124, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3119, hc06, hlam, p0_1]
                · linarith only [h3102, h3119, hc06, hlam, p0_1]
                · linarith only [h3119, hc06, hlam, p0_1]
                · linarith only [h3104, h3119, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3131 | h3131
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3132 | h3132
                    · linarith only [h3101, h3132, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3131, h3132, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3135 | h3135
                    · linarith only [h3101, h3135, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3135, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h3138 | h3138
              · rcases h6emax with h3139 | h3139 | h3139 | h3139 | h3139 | h3139
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3140 | h3140
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3141 | h3141
                    · linarith only [h3101, h3141, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3139, h3140, h3141, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3144 | h3144
                    · linarith only [h3101, h3144, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3144, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3139, hc06, hlam, p0_1]
                · linarith only [h3102, h3139, hc06, hlam, p0_1]
                · linarith only [h3139, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3150 | h3150
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3151 | h3151
                    · linarith only [h3101, h3151, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3150, h3151, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3154 | h3154
                    · linarith only [h3101, h3154, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3154, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3138, h3139, hc06, hlam, p0_1]
              · rcases h6emax with h3158 | h3158 | h3158 | h3158 | h3158 | h3158
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3159 | h3159
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3160 | h3160
                    · linarith only [h3101, h3160, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3158, h3159, h3160, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3163 | h3163
                    · linarith only [h3101, h3159, h3163, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3163, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3158, hc06, hlam, p0_1]
                · linarith only [h3102, h3158, hc06, hlam, p0_1]
                · linarith only [h3158, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3169 | h3169
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3170 | h3170
                    · linarith only [h3101, h3170, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3170, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3173 | h3173
                    · linarith only [h3101, h3169, h3173, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3173, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3176 | h3176
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3177 | h3177
                    · linarith only [h3101, h3177, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3177, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3180 | h3180
                    · linarith only [h3101, h3176, h3180, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3180, hc01, hc16, hlam, hphi, p0_1]
          · linarith only [h3103, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3184 | h3184
          · rcases p0_3 (m.d 4 6) (by simp) with h3185 | h3185
            · rcases p0_3 (m.d 5 6) (by simp) with h3186 | h3186
              · rcases h6emax with h3187 | h3187 | h3187 | h3187 | h3187 | h3187
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3188 | h3188
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3189 | h3189
                    · linarith only [h3101, h3189, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3187, h3188, h3189, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3192 | h3192
                    · linarith only [h3101, h3192, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3192, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3187, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3196 | h3196
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3197 | h3197
                    · linarith only [h3101, h3197, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3197, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3200 | h3200
                    · linarith only [h3101, h3200, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3200, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3187, hc06, hlam, p0_1]
                · linarith only [h3185, h3187, hc06, hlam, p0_1]
                · linarith only [h3186, h3187, hc06, hlam, p0_1]
              · rcases h6emax with h3206 | h3206 | h3206 | h3206 | h3206 | h3206
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3207 | h3207
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3208 | h3208
                    · linarith only [h3101, h3208, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3206, h3207, h3208, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3211 | h3211
                    · linarith only [h3101, h3207, h3211, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3211, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3206, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3215 | h3215
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3216 | h3216
                    · linarith only [h3101, h3216, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3215, h3216, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3219 | h3219
                    · linarith only [h3101, h3219, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3219, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3206, hc06, hlam, p0_1]
                · linarith only [h3185, h3206, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3224 | h3224
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3225 | h3225
                    · linarith only [h3101, h3225, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3225, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3228 | h3228
                    · linarith only [h3101, h3224, h3228, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3228, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h3231 | h3231
              · rcases h6emax with h3232 | h3232 | h3232 | h3232 | h3232 | h3232
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3233 | h3233
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3234 | h3234
                    · linarith only [h3101, h3234, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3234, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3237 | h3237
                    · linarith only [h3101, h3233, h3237, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3237, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3232, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3241 | h3241
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3242 | h3242
                    · linarith only [h3101, h3242, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3241, h3242, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3245 | h3245
                    · linarith only [h3101, h3245, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3245, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3232, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3249 | h3249
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3250 | h3250
                    · linarith only [h3101, h3250, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3249, h3250, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3253 | h3253
                    · linarith only [h3101, h3253, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3253, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3231, h3232, hc06, hlam, p0_1]
              · rcases h6emax with h3257 | h3257 | h3257 | h3257 | h3257 | h3257
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3258 | h3258
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3259 | h3259
                    · linarith only [h3101, h3259, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3257, h3258, h3259, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3262 | h3262
                    · linarith only [h3101, h3262, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3262, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3101, h3257, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3266 | h3266
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3267 | h3267
                    · linarith only [h3101, h3267, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3266, h3267, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3270 | h3270
                    · linarith only [h3101, h3266, h3270, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3270, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3257, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3274 | h3274
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3275 | h3275
                    · linarith only [h3101, h3275, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3275, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3278 | h3278
                    · linarith only [h3101, h3274, h3278, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3278, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3281 | h3281
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3282 | h3282
                    · linarith only [h3101, h3282, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3101, h3282, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3285 | h3285
                    · linarith only [h3101, h3281, h3285, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3101, h3285, hc01, hc16, hlam, hphi, p0_1]
          · linarith only [h3184, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h3289 | h3289
        · rcases p0_3 (m.d 3 6) (by simp) with h3290 | h3290
          · rcases p0_3 (m.d 4 6) (by simp) with h3291 | h3291
            · rcases p0_3 (m.d 5 6) (by simp) with h3292 | h3292
              · rcases h6emax with h3293 | h3293 | h3293 | h3293 | h3293 | h3293
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3294 | h3294
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3295 | h3295
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3296 | h3296
                      · linarith only [h3289, h3294, h3295, h3296, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h3292, h3296, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3295, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3300 | h3300
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3301 | h3301
                      · linarith only [h3289, h3300, h3301, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3292, h3294, h3301, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3300, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3305 | h3305
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3306 | h3306
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3307 | h3307
                      · linarith only [h3289, h3306, h3307, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3292, h3307, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3306, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3311 | h3311
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3312 | h3312
                      · linarith only [h3289, h3311, h3312, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3292, h3305, h3312, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3311, hlam]
                · linarith only [h3289, h3293, hc06, hlam, p0_1]
                · linarith only [h3293, hc06, hlam, p0_1]
                · linarith only [h3291, h3293, hc06, hlam, p0_1]
                · linarith only [h3292, h3293, hc06, hlam, p0_1]
              · rcases h6emax with h3320 | h3320 | h3320 | h3320 | h3320 | h3320
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3321 | h3321
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3322 | h3322
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3323 | h3323
                      · linarith only [h3289, h3322, h3323, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3323, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3322, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3327 | h3327
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3328 | h3328
                      · linarith only [h3289, h3328, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3321, h3328, hc01, hc26, hlam, hphi, ht12, p0_1]
                    · linarith only [h3101, h3327, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3332 | h3332
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3333 | h3333
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3334 | h3334
                      · linarith only [h3289, h3334, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3334, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3333, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3338 | h3338
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3339 | h3339
                      · linarith only [h3289, h3339, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3339, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3338, hlam]
                · linarith only [h3289, h3320, hc06, hlam, p0_1]
                · linarith only [h3320, hc06, hlam, p0_1]
                · linarith only [h3291, h3320, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3346 | h3346
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3347 | h3347
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3348 | h3348
                      · linarith only [h3289, h3347, h3348, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3348, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3347, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3352 | h3352
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3353 | h3353
                      · linarith only [h3289, h3353, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3353, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3352, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h3357 | h3357
              · rcases h6emax with h3358 | h3358 | h3358 | h3358 | h3358 | h3358
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3359 | h3359
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3360 | h3360
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3361 | h3361
                      · linarith only [h3289, h3360, h3361, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3357, h3361, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3360, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3365 | h3365
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3366 | h3366
                      · linarith only [h3289, h3365, h3366, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3357, h3366, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3365, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3370 | h3370
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3371 | h3371
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3372 | h3372
                      · linarith only [h3289, h3371, h3372, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3357, h3372, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3371, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3376 | h3376
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3377 | h3377
                      · linarith only [h3289, h3376, h3377, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3357, h3370, h3377, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3376, hlam]
                · linarith only [h3289, h3358, hc06, hlam, p0_1]
                · linarith only [h3358, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3383 | h3383
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3384 | h3384
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3385 | h3385
                      · linarith only [h3289, h3384, h3385, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3357, h3385, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3384, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3389 | h3389
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3390 | h3390
                      · linarith only [h3289, h3389, h3390, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3357, h3383, h3390, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h3101, h3389, hlam]
                · linarith only [h3357, h3358, hc06, hlam, p0_1]
              · rcases h6emax with h3395 | h3395 | h3395 | h3395 | h3395 | h3395
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3396 | h3396
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3397 | h3397
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3398 | h3398
                      · linarith only [h3289, h3397, h3398, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3398, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3397, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3402 | h3402
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3403 | h3403
                      · linarith only [h3289, h3403, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3403, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3402, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3407 | h3407
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3408 | h3408
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3409 | h3409
                      · linarith only [h3289, h3409, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3409, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3408, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3413 | h3413
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3414 | h3414
                      · linarith only [h3289, h3414, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3414, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3413, hlam]
                · linarith only [h3289, h3395, hc06, hlam, p0_1]
                · linarith only [h3395, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3420 | h3420
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3421 | h3421
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3422 | h3422
                      · linarith only [h3289, h3421, h3422, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3422, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3421, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3426 | h3426
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3427 | h3427
                      · linarith only [h3289, h3427, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3427, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3426, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3431 | h3431
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3432 | h3432
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3433 | h3433
                      · linarith only [h3289, h3433, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3433, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3432, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3437 | h3437
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3438 | h3438
                      · linarith only [h3289, h3438, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h3289, h3438, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h3101, h3437, hlam]
          · linarith only [h3290, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3443 | h3443
          · rcases p0_3 (m.d 4 6) (by simp) with h3444 | h3444
            · rcases p0_3 (m.d 5 6) (by simp) with h3445 | h3445
              · rcases h6emax with h3446 | h3446 | h3446 | h3446 | h3446 | h3446
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3447 | h3447
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3448 | h3448
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3449 | h3449
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3450 | h3450
                        · linarith only [h3450, hlam, p0_0]
                        · linarith only [h3445, h3450, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3449, hlam]
                    · linarith only [h3101, h3448, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3455 | h3455
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3456 | h3456
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3457 | h3457
                        · linarith only [h3457, hlam, p0_0]
                        · linarith only [h3445, h3457, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3456, hlam]
                    · linarith only [h3101, h3455, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3462 | h3462
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3463 | h3463
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3464 | h3464
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3465 | h3465
                        · linarith only [h3465, hlam, p0_0]
                        · linarith only [h3445, h3465, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3464, hlam]
                    · linarith only [h3101, h3463, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3470 | h3470
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3471 | h3471
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3472 | h3472
                        · linarith only [h3472, hlam, p0_0]
                        · linarith only [h3445, h3472, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3471, hlam]
                    · linarith only [h3101, h3470, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3477 | h3477
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3478 | h3478
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3479 | h3479
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3480 | h3480
                        · linarith only [h3480, hlam, p0_0]
                        · linarith only [h3445, h3480, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3479, hlam]
                    · linarith only [h3101, h3478, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3485 | h3485
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3486 | h3486
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3487 | h3487
                        · linarith only [h3487, hlam, p0_0]
                        · linarith only [h3445, h3487, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3486, hlam]
                    · linarith only [h3101, h3485, hlam]
                · linarith only [h3446, hc06, hlam, p0_1]
                · linarith only [h3444, h3446, hc06, hlam, p0_1]
                · linarith only [h3445, h3446, hc06, hlam, p0_1]
              · rcases h6emax with h3495 | h3495 | h3495 | h3495 | h3495 | h3495
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3496 | h3496
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3497 | h3497
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3498 | h3498
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3499 | h3499
                        · linarith only [h3499, hlam, p0_0]
                        · linarith only [h3499, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3498, hlam]
                    · linarith only [h3101, h3497, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3504 | h3504
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3505 | h3505
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3506 | h3506
                        · linarith only [h3506, hlam, p0_0]
                        · linarith only [h3444, h3506, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h3289, h3505, hlam]
                    · linarith only [h3101, h3504, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3511 | h3511
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3512 | h3512
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3513 | h3513
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3514 | h3514
                        · linarith only [h3514, hlam, p0_0]
                        · linarith only [h3444, h3514, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h3289, h3513, hlam]
                    · linarith only [h3101, h3512, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3519 | h3519
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3520 | h3520
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3521 | h3521
                        · linarith only [h3521, hlam, p0_0]
                        · linarith only [h3444, h3521, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h3289, h3520, hlam]
                    · linarith only [h3101, h3519, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3526 | h3526
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3527 | h3527
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3528 | h3528
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3529 | h3529
                        · linarith only [h3529, hlam, p0_0]
                        · linarith only [h3444, h3529, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h3289, h3528, hlam]
                    · linarith only [h3101, h3527, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3534 | h3534
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3535 | h3535
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3536 | h3536
                        · linarith only [h3536, hlam, p0_0]
                        · linarith only [h3444, h3536, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h3289, h3535, hlam]
                    · linarith only [h3101, h3534, hlam]
                · linarith only [h3495, hc06, hlam, p0_1]
                · linarith only [h3444, h3495, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3543 | h3543
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3544 | h3544
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3545 | h3545
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3546 | h3546
                        · linarith only [h3546, hlam, p0_0]
                        · linarith only [h3546, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3545, hlam]
                    · linarith only [h3101, h3544, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3551 | h3551
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3552 | h3552
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3553 | h3553
                        · linarith only [h3553, hlam, p0_0]
                        · linarith only [h3444, h3553, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h3289, h3552, hlam]
                    · linarith only [h3101, h3551, hlam]
            · rcases p0_3 (m.d 5 6) (by simp) with h3558 | h3558
              · rcases h6emax with h3559 | h3559 | h3559 | h3559 | h3559 | h3559
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3560 | h3560
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3561 | h3561
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3562 | h3562
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3563 | h3563
                        · linarith only [h3563, hlam, p0_0]
                        · linarith only [h3558, h3563, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3562, hlam]
                    · linarith only [h3101, h3561, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3568 | h3568
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3569 | h3569
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3570 | h3570
                        · linarith only [h3570, hlam, p0_0]
                        · linarith only [h3558, h3570, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3569, hlam]
                    · linarith only [h3101, h3568, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3575 | h3575
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3576 | h3576
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3577 | h3577
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3578 | h3578
                        · linarith only [h3578, hlam, p0_0]
                        · linarith only [h3558, h3578, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3577, hlam]
                    · linarith only [h3101, h3576, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3583 | h3583
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3584 | h3584
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3585 | h3585
                        · linarith only [h3585, hlam, p0_0]
                        · linarith only [h3558, h3585, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3584, hlam]
                    · linarith only [h3101, h3583, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3590 | h3590
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3591 | h3591
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3592 | h3592
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3593 | h3593
                        · linarith only [h3593, hlam, p0_0]
                        · linarith only [h3558, h3593, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3592, hlam]
                    · linarith only [h3101, h3591, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3598 | h3598
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3599 | h3599
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3600 | h3600
                        · linarith only [h3600, hlam, p0_0]
                        · linarith only [h3558, h3600, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3599, hlam]
                    · linarith only [h3101, h3598, hlam]
                · linarith only [h3559, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3606 | h3606
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3607 | h3607
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3608 | h3608
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3609 | h3609
                        · linarith only [h3609, hlam, p0_0]
                        · linarith only [h3558, h3609, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3608, hlam]
                    · linarith only [h3101, h3607, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3614 | h3614
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3615 | h3615
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3616 | h3616
                        · linarith only [h3616, hlam, p0_0]
                        · linarith only [h3558, h3616, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h3289, h3615, hlam]
                    · linarith only [h3101, h3614, hlam]
                · linarith only [h3558, h3559, hc06, hlam, p0_1]
              · rcases h6emax with h3622 | h3622 | h3622 | h3622 | h3622 | h3622
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3623 | h3623
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3624 | h3624
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3625 | h3625
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3626 | h3626
                        · linarith only [h3626, hlam, p0_0]
                        · linarith only [h3626, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3625, hlam]
                    · linarith only [h3101, h3624, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3631 | h3631
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3632 | h3632
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3633 | h3633
                        · linarith only [h3633, hlam, p0_0]
                        · linarith only [h3633, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3632, hlam]
                    · linarith only [h3101, h3631, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3638 | h3638
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3639 | h3639
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3640 | h3640
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3641 | h3641
                        · linarith only [h3641, hlam, p0_0]
                        · linarith only [h3641, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3640, hlam]
                    · linarith only [h3101, h3639, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3646 | h3646
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3647 | h3647
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3648 | h3648
                        · linarith only [h3648, hlam, p0_0]
                        · linarith only [h3648, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3647, hlam]
                    · linarith only [h3101, h3646, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3653 | h3653
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3654 | h3654
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3655 | h3655
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3656 | h3656
                        · linarith only [h3656, hlam, p0_0]
                        · linarith only [h3656, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3655, hlam]
                    · linarith only [h3101, h3654, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3661 | h3661
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3662 | h3662
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3663 | h3663
                        · linarith only [h3663, hlam, p0_0]
                        · linarith only [h3663, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3662, hlam]
                    · linarith only [h3101, h3661, hlam]
                · linarith only [h3622, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3669 | h3669
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3670 | h3670
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3671 | h3671
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3672 | h3672
                        · linarith only [h3672, hlam, p0_0]
                        · linarith only [h3672, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3671, hlam]
                    · linarith only [h3101, h3670, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3677 | h3677
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3678 | h3678
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3679 | h3679
                        · linarith only [h3679, hlam, p0_0]
                        · linarith only [h3679, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3678, hlam]
                    · linarith only [h3101, h3677, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3684 | h3684
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3685 | h3685
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3686 | h3686
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3687 | h3687
                        · linarith only [h3687, hlam, p0_0]
                        · linarith only [h3687, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3686, hlam]
                    · linarith only [h3101, h3685, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3692 | h3692
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h3693 | h3693
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h3694 | h3694
                        · linarith only [h3694, hlam, p0_0]
                        · linarith only [h3694, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h3289, h3693, hlam]
                    · linarith only [h3101, h3692, hlam]
          · linarith only [h3443, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h3700 | h3700
    · linarith only [h3700, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h3702 | h3702
      · linarith only [h3702, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h3704 | h3704
        · rcases p0_3 (m.d 3 6) (by simp) with h3705 | h3705
          · rcases p0_3 (m.d 4 6) (by simp) with h3706 | h3706
            · rcases p0_3 (m.d 5 6) (by simp) with h3707 | h3707
              · rcases h6emax with h3708 | h3708 | h3708 | h3708 | h3708 | h3708
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3709 | h3709
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3710 | h3710
                    · linarith only [h3700, h3710, hlam]
                    · linarith only [h3707, h3709, h3710, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3713 | h3713
                    · linarith only [h3700, h3713, hlam]
                    · linarith only [h3707, h3713, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3716 | h3716
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3717 | h3717
                    · linarith only [h3700, h3717, hlam]
                    · linarith only [h3707, h3716, h3717, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3720 | h3720
                    · linarith only [h3700, h3720, hlam]
                    · linarith only [h3707, h3720, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3704, h3708, hc16, hlam, p0_1]
                · linarith only [h3708, hc16, hlam, p0_1]
                · linarith only [h3706, h3708, hc16, hlam, p0_1]
                · linarith only [h3707, h3708, hc16, hlam, p0_1]
              · rcases h6emax with h3727 | h3727 | h3727 | h3727 | h3727 | h3727
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3728 | h3728
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3729 | h3729
                    · linarith only [h3700, h3729, hlam]
                    · linarith only [h3704, h3728, h3729, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3732 | h3732
                    · linarith only [h3700, h3732, hlam]
                    · linarith only [h3706, h3732, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3735 | h3735
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3736 | h3736
                    · linarith only [h3700, h3736, hlam]
                    · linarith only [h3706, h3735, h3736, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3739 | h3739
                    · linarith only [h3700, h3739, hlam]
                    · linarith only [h3706, h3739, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h3704, h3727, hc16, hlam, p0_1]
                · linarith only [h3727, hc16, hlam, p0_1]
                · linarith only [h3706, h3727, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3745 | h3745
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3746 | h3746
                    · linarith only [h3700, h3746, hlam]
                    · linarith only [h3704, h3745, h3746, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3749 | h3749
                    · linarith only [h3700, h3749, hlam]
                    · linarith only [h3706, h3749, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h3752 | h3752
              · rcases h6emax with h3753 | h3753 | h3753 | h3753 | h3753 | h3753
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3754 | h3754
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3755 | h3755
                    · linarith only [h3700, h3755, hlam]
                    · linarith only [h3752, h3754, h3755, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3758 | h3758
                    · linarith only [h3700, h3758, hlam]
                    · linarith only [h3752, h3758, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3761 | h3761
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3762 | h3762
                    · linarith only [h3700, h3762, hlam]
                    · linarith only [h3752, h3762, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3765 | h3765
                    · linarith only [h3700, h3765, hlam]
                    · linarith only [h3752, h3765, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3704, h3753, hc16, hlam, p0_1]
                · linarith only [h3753, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3770 | h3770
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3771 | h3771
                    · linarith only [h3700, h3771, hlam]
                    · linarith only [h3752, h3771, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3774 | h3774
                    · linarith only [h3700, h3774, hlam]
                    · linarith only [h3752, h3774, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3752, h3753, hc16, hlam, p0_1]
              · rcases h6emax with h3778 | h3778 | h3778 | h3778 | h3778 | h3778
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3779 | h3779
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3780 | h3780
                    · linarith only [h3700, h3780, hlam]
                    · linarith only [h3704, h3779, h3780, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3783 | h3783
                    · linarith only [h3700, h3783, hlam]
                    · linarith only [h3783, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3786 | h3786
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3787 | h3787
                    · linarith only [h3700, h3787, hlam]
                    · linarith only [h3787, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3790 | h3790
                    · linarith only [h3700, h3790, hlam]
                    · linarith only [h3790, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h3704, h3778, hc16, hlam, p0_1]
                · linarith only [h3778, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3795 | h3795
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3796 | h3796
                    · linarith only [h3700, h3796, hlam]
                    · linarith only [h3704, h3796, hc01, hc26, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3799 | h3799
                    · linarith only [h3700, h3799, hlam]
                    · linarith only [h3799, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3802 | h3802
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3803 | h3803
                    · linarith only [h3700, h3803, hlam]
                    · linarith only [h3802, h3803, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3806 | h3806
                    · linarith only [h3700, h3806, hlam]
                    · linarith only [h3806, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h3705, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3810 | h3810
          · rcases p0_3 (m.d 4 6) (by simp) with h3811 | h3811
            · rcases p0_3 (m.d 5 6) (by simp) with h3812 | h3812
              · rcases h6emax with h3813 | h3813 | h3813 | h3813 | h3813 | h3813
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3814 | h3814
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3815 | h3815
                    · linarith only [h3700, h3815, hlam]
                    · linarith only [h3812, h3814, h3815, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3818 | h3818
                    · linarith only [h3700, h3818, hlam]
                    · linarith only [h3812, h3818, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3821 | h3821
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3822 | h3822
                    · linarith only [h3700, h3822, hlam]
                    · linarith only [h3812, h3821, h3822, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3825 | h3825
                    · linarith only [h3700, h3825, hlam]
                    · linarith only [h3812, h3825, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3828 | h3828
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3829 | h3829
                    · linarith only [h3700, h3829, hlam]
                    · linarith only [h3812, h3829, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3832 | h3832
                    · linarith only [h3700, h3832, hlam]
                    · linarith only [h3812, h3832, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3813, hc16, hlam, p0_1]
                · linarith only [h3811, h3813, hc16, hlam, p0_1]
                · linarith only [h3812, h3813, hc16, hlam, p0_1]
              · rcases h6emax with h3838 | h3838 | h3838 | h3838 | h3838 | h3838
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3839 | h3839
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3840 | h3840
                    · linarith only [h3700, h3840, hlam]
                    · linarith only [h3840, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3843 | h3843
                    · linarith only [h3700, h3843, hlam]
                    · linarith only [h3811, h3843, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3846 | h3846
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3847 | h3847
                    · linarith only [h3700, h3847, hlam]
                    · linarith only [h3811, h3846, h3847, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3850 | h3850
                    · linarith only [h3700, h3850, hlam]
                    · linarith only [h3811, h3850, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3853 | h3853
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3854 | h3854
                    · linarith only [h3700, h3854, hlam]
                    · linarith only [h3811, h3853, h3854, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3857 | h3857
                    · linarith only [h3700, h3857, hlam]
                    · linarith only [h3811, h3857, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h3838, hc16, hlam, p0_1]
                · linarith only [h3811, h3838, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3862 | h3862
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3863 | h3863
                    · linarith only [h3700, h3863, hlam]
                    · linarith only [h3863, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3866 | h3866
                    · linarith only [h3700, h3866, hlam]
                    · linarith only [h3811, h3866, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h3869 | h3869
              · rcases h6emax with h3870 | h3870 | h3870 | h3870 | h3870 | h3870
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3871 | h3871
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3872 | h3872
                    · linarith only [h3700, h3872, hlam]
                    · linarith only [h3869, h3872, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3875 | h3875
                    · linarith only [h3700, h3875, hlam]
                    · linarith only [h3869, h3875, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3878 | h3878
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3879 | h3879
                    · linarith only [h3700, h3879, hlam]
                    · linarith only [h3869, h3879, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3882 | h3882
                    · linarith only [h3700, h3882, hlam]
                    · linarith only [h3869, h3882, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3885 | h3885
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3886 | h3886
                    · linarith only [h3700, h3886, hlam]
                    · linarith only [h3869, h3885, h3886, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3889 | h3889
                    · linarith only [h3700, h3889, hlam]
                    · linarith only [h3869, h3889, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3870, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3893 | h3893
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3894 | h3894
                    · linarith only [h3700, h3894, hlam]
                    · linarith only [h3869, h3893, h3894, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3897 | h3897
                    · linarith only [h3700, h3897, hlam]
                    · linarith only [h3869, h3897, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3869, h3870, hc16, hlam, p0_1]
              · rcases h6emax with h3901 | h3901 | h3901 | h3901 | h3901 | h3901
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3902 | h3902
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3903 | h3903
                    · linarith only [h3700, h3903, hlam]
                    · linarith only [h3902, h3903, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3906 | h3906
                    · linarith only [h3700, h3906, hlam]
                    · linarith only [h3906, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3909 | h3909
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3910 | h3910
                    · linarith only [h3700, h3910, hlam]
                    · linarith only [h3909, h3910, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3913 | h3913
                    · linarith only [h3700, h3913, hlam]
                    · linarith only [h3913, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3916 | h3916
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3917 | h3917
                    · linarith only [h3700, h3917, hlam]
                    · linarith only [h3917, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3920 | h3920
                    · linarith only [h3700, h3920, hlam]
                    · linarith only [h3920, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h3901, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3924 | h3924
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3925 | h3925
                    · linarith only [h3700, h3925, hlam]
                    · linarith only [h3925, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3928 | h3928
                    · linarith only [h3700, h3928, hlam]
                    · linarith only [h3928, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3931 | h3931
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3932 | h3932
                    · linarith only [h3700, h3932, hlam]
                    · linarith only [h3932, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3935 | h3935
                    · linarith only [h3700, h3935, hlam]
                    · linarith only [h3935, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h3810, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h3939 | h3939
    · linarith only [h3939, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h3941 | h3941
      · rcases p0_3 (m.d 2 6) (by simp) with h3942 | h3942
        · linarith only [h3942, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h3944 | h3944
          · rcases p0_3 (m.d 4 6) (by simp) with h3945 | h3945
            · rcases p0_3 (m.d 5 6) (by simp) with h3946 | h3946
              · rcases h6emax with h3947 | h3947 | h3947 | h3947 | h3947 | h3947
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3948 | h3948
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3949 | h3949
                    · linarith only [h3941, h3949, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h3949, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3952 | h3952
                    · linarith only [h3939, h3941, h3952, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h3952, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3941, h3947, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3956 | h3956
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3957 | h3957
                    · linarith only [h3939, h3941, h3957, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h3957, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3960 | h3960
                    · linarith only [h3939, h3941, h3956, h3960, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h3960, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3947, hc06, hlam, p0_1]
                · linarith only [h3939, h3945, h3947, hc06, hlam, p0_1]
                · linarith only [h3939, h3946, h3947, hc06, hlam, p0_1]
              · rcases h6emax with h3966 | h3966 | h3966 | h3966 | h3966 | h3966
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3967 | h3967
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3968 | h3968
                    · linarith only [h3941, h3968, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h3968, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3971 | h3971
                    · linarith only [h3939, h3941, h3967, h3971, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h3971, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3941, h3966, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3975 | h3975
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3976 | h3976
                    · linarith only [h3939, h3941, h3976, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h3976, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3979 | h3979
                    · linarith only [h3939, h3941, h3975, h3979, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h3979, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3966, hc06, hlam, p0_1]
                · linarith only [h3939, h3945, h3966, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3984 | h3984
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3985 | h3985
                    · linarith only [h3939, h3941, h3985, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h3985, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3988 | h3988
                    · linarith only [h3939, h3941, h3984, h3988, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h3988, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h3991 | h3991
              · rcases h6emax with h3992 | h3992 | h3992 | h3992 | h3992 | h3992
                · rcases m.htr 0 1 2 (by decide) (by decide) with h3993 | h3993
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3994 | h3994
                    · linarith only [h3939, h3941, h3994, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h3994, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h3997 | h3997
                    · linarith only [h3939, h3941, h3993, h3997, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h3997, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3941, h3992, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4001 | h4001
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4002 | h4002
                    · linarith only [h3939, h3941, h4002, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4001, h4002, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4005 | h4005
                    · linarith only [h3939, h3941, h4005, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4005, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3992, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4009 | h4009
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4010 | h4010
                    · linarith only [h3939, h3941, h4010, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4009, h4010, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4013 | h4013
                    · linarith only [h3939, h3941, h4013, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4013, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3991, h3992, hc06, hlam, p0_1]
              · rcases h6emax with h4017 | h4017 | h4017 | h4017 | h4017 | h4017
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4018 | h4018
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4019 | h4019
                    · linarith only [h3939, h3941, h4019, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4019, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4022 | h4022
                    · linarith only [h3939, h3941, h4018, h4022, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h4022, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h3941, h4017, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4026 | h4026
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4027 | h4027
                    · linarith only [h3939, h3941, h4027, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4026, h4027, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4030 | h4030
                    · linarith only [h3939, h3941, h4030, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4030, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h3939, h4017, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4034 | h4034
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4035 | h4035
                    · linarith only [h3939, h3941, h4035, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4035, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4038 | h4038
                    · linarith only [h3939, h3941, h4034, h4038, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h4038, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4041 | h4041
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4042 | h4042
                    · linarith only [h3939, h3941, h4042, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h3939, h3941, h4041, h4042, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4045 | h4045
                    · linarith only [h3939, h3941, h4041, h4045, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h3939, h3941, h4045, hc01, hc16, hlam, hphi, p0_1]
          · linarith only [h3944, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h4049 | h4049
        · linarith only [h4049, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h4051 | h4051
          · rcases p0_3 (m.d 4 6) (by simp) with h4052 | h4052
            · rcases p0_3 (m.d 5 6) (by simp) with h4053 | h4053
              · rcases h6emax with h4054 | h4054 | h4054 | h4054 | h4054 | h4054
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4055 | h4055
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4056 | h4056
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4057 | h4057
                      · linarith only [h3939, h4057, hlam]
                      · linarith only [h4053, h4057, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3941, h4053, h4056, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4061 | h4061
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4062 | h4062
                      · linarith only [h3939, h4062, hlam]
                      · linarith only [h4053, h4055, h4061, h4062, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h3941, h4053, h4061, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4066 | h4066
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4067 | h4067
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4068 | h4068
                      · linarith only [h3939, h4068, hlam]
                      · linarith only [h4053, h4066, h4068, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4054, h4066, h4067, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4072 | h4072
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4073 | h4073
                      · linarith only [h3939, h4073, hlam]
                      · linarith only [h4053, h4066, h4073, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h4054, h4072, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4077 | h4077
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4078 | h4078
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4079 | h4079
                      · linarith only [h3939, h4079, hlam]
                      · linarith only [h4053, h4079, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3941, h4053, h4078, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4083 | h4083
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4084 | h4084
                      · linarith only [h3939, h4084, hlam]
                      · linarith only [h4053, h4077, h4083, h4084, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h3941, h4053, h4083, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3941, h4054, hc16, hlam, p0_1]
                · linarith only [h3941, h4052, h4054, hc16, hlam, p0_1]
                · linarith only [h3941, h4053, h4054, hc16, hlam, p0_1]
              · rcases h6emax with h4091 | h4091 | h4091 | h4091 | h4091 | h4091
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4092 | h4092
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4093 | h4093
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4094 | h4094
                      · linarith only [h3939, h4094, hlam]
                      · linarith only [h4052, h4094, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h3941, h4052, h4092, h4093, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4098 | h4098
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4099 | h4099
                      · linarith only [h3939, h4099, hlam]
                      · linarith only [h4052, h4092, h4098, h4099, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h3941, h4052, h4098, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4103 | h4103
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4104 | h4104
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4105 | h4105
                      · linarith only [h3939, h4105, hlam]
                      · linarith only [h4052, h4103, h4105, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h4091, h4103, h4104, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4109 | h4109
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4110 | h4110
                      · linarith only [h3939, h4110, hlam]
                      · linarith only [h4052, h4103, h4109, h4110, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h4091, h4109, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4114 | h4114
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4115 | h4115
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4116 | h4116
                      · linarith only [h3939, h4116, hlam]
                      · linarith only [h4052, h4114, h4116, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h3941, h4052, h4114, h4115, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4120 | h4120
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4121 | h4121
                      · linarith only [h3939, h4121, hlam]
                      · linarith only [h4052, h4114, h4121, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h3941, h4052, h4120, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h3941, h4091, hc16, hlam, p0_1]
                · linarith only [h3941, h4052, h4091, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4127 | h4127
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4128 | h4128
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4129 | h4129
                      · linarith only [h3939, h4129, hlam]
                      · linarith only [h4052, h4129, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h3941, h4052, h4128, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4133 | h4133
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4134 | h4134
                      · linarith only [h3939, h4134, hlam]
                      · linarith only [h4052, h4127, h4133, h4134, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h3941, h4052, h4133, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h4138 | h4138
              · rcases h6emax with h4139 | h4139 | h4139 | h4139 | h4139 | h4139
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4140 | h4140
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4141 | h4141
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4142 | h4142
                      · linarith only [h3939, h4142, hlam]
                      · linarith only [h4138, h4142, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3941, h4138, h4140, h4141, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4146 | h4146
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4147 | h4147
                      · linarith only [h3939, h4147, hlam]
                      · linarith only [h4138, h4140, h4146, h4147, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h3941, h4138, h4146, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4151 | h4151
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4152 | h4152
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4153 | h4153
                      · linarith only [h3939, h4153, hlam]
                      · linarith only [h4138, h4151, h4153, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4139, h4151, h4152, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4157 | h4157
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4158 | h4158
                      · linarith only [h3939, h4158, hlam]
                      · linarith only [h4138, h4151, h4158, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h4139, h4157, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4162 | h4162
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4163 | h4163
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4164 | h4164
                      · linarith only [h3939, h4164, hlam]
                      · linarith only [h4138, h4164, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3941, h4138, h4163, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4168 | h4168
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4169 | h4169
                      · linarith only [h3939, h4169, hlam]
                      · linarith only [h4138, h4162, h4168, h4169, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h3941, h4138, h4168, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3941, h4139, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4174 | h4174
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4175 | h4175
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4176 | h4176
                      · linarith only [h3939, h4176, hlam]
                      · linarith only [h4138, h4176, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h3941, h4138, h4174, h4175, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4180 | h4180
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4181 | h4181
                      · linarith only [h3939, h4181, hlam]
                      · linarith only [h4138, h4174, h4181, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h3941, h4138, h4180, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h3941, h4138, h4139, hc16, hlam, p0_1]
              · rcases h6emax with h4186 | h4186 | h4186 | h4186 | h4186 | h4186
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4187 | h4187
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4188 | h4188
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4189 | h4189
                      · linarith only [h3939, h4189, hlam]
                      · linarith only [h4189, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h3941, h4187, h4188, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4193 | h4193
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4194 | h4194
                      · linarith only [h3939, h4194, hlam]
                      · linarith only [h4187, h4194, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h3941, h4193, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4198 | h4198
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4199 | h4199
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4200 | h4200
                      · linarith only [h3939, h4200, hlam]
                      · linarith only [h4200, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4186, h4199, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4204 | h4204
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4205 | h4205
                      · linarith only [h3939, h4205, hlam]
                      · linarith only [h4198, h4204, h4205, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h4186, h4204, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4209 | h4209
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4210 | h4210
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4211 | h4211
                      · linarith only [h3939, h4211, hlam]
                      · linarith only [h4211, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h3941, h4209, h4210, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4215 | h4215
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4216 | h4216
                      · linarith only [h3939, h4216, hlam]
                      · linarith only [h4209, h4216, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h3941, h4215, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h3941, h4186, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4221 | h4221
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4222 | h4222
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4223 | h4223
                      · linarith only [h3939, h4223, hlam]
                      · linarith only [h4223, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h3941, h4222, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4227 | h4227
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4228 | h4228
                      · linarith only [h3939, h4228, hlam]
                      · linarith only [h4221, h4227, h4228, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h3941, h4227, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4232 | h4232
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4233 | h4233
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4234 | h4234
                      · linarith only [h3939, h4234, hlam]
                      · linarith only [h4234, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h3941, h4232, h4233, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4238 | h4238
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4239 | h4239
                      · linarith only [h3939, h4239, hlam]
                      · linarith only [h4232, h4238, h4239, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h3941, h4238, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h4051, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h4245 | h4245
    · linarith only [h4245, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h4247 | h4247
      · rcases p0_3 (m.d 2 6) (by simp) with h4248 | h4248
        · rcases p0_3 (m.d 3 6) (by simp) with h4249 | h4249
          · rcases p0_3 (m.d 4 6) (by simp) with h4250 | h4250
            · linarith only [h4250, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h4252 | h4252
              · rcases h6emax with h4253 | h4253 | h4253 | h4253 | h4253 | h4253
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4254 | h4254
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4255 | h4255
                    · linarith only [h4247, h4255, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4255, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4258 | h4258
                    · linarith only [h4245, h4247, h4254, h4258, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4258, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4247, h4253, hc06, hlam, p0_1]
                · linarith only [h4245, h4248, h4253, hc06, hlam, p0_1]
                · linarith only [h4245, h4253, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4264 | h4264
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4265 | h4265
                    · linarith only [h4245, h4247, h4265, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4264, h4265, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4268 | h4268
                    · linarith only [h4245, h4247, h4268, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4268, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4252, h4253, hc06, hlam, p0_1]
              · rcases h6emax with h4272 | h4272 | h4272 | h4272 | h4272 | h4272
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4273 | h4273
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4274 | h4274
                    · linarith only [h4245, h4247, h4274, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4274, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4277 | h4277
                    · linarith only [h4245, h4247, h4273, h4277, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4277, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4247, h4272, hc06, hlam, p0_1]
                · linarith only [h4245, h4248, h4272, hc06, hlam, p0_1]
                · linarith only [h4245, h4272, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4283 | h4283
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4284 | h4284
                    · linarith only [h4245, h4247, h4284, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4284, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4287 | h4287
                    · linarith only [h4245, h4247, h4283, h4287, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4287, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4290 | h4290
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4291 | h4291
                    · linarith only [h4245, h4247, h4291, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4291, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4294 | h4294
                    · linarith only [h4245, h4247, h4290, h4294, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4294, hc01, hc16, hlam, hphi, p0_1]
          · linarith only [h4249, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h4298 | h4298
          · rcases p0_3 (m.d 4 6) (by simp) with h4299 | h4299
            · linarith only [h4299, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h4301 | h4301
              · rcases h6emax with h4302 | h4302 | h4302 | h4302 | h4302 | h4302
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4303 | h4303
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4304 | h4304
                    · linarith only [h4245, h4247, h4304, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4304, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4307 | h4307
                    · linarith only [h4245, h4247, h4303, h4307, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4307, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4247, h4302, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4311 | h4311
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4312 | h4312
                    · linarith only [h4245, h4247, h4312, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4312, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4315 | h4315
                    · linarith only [h4245, h4247, h4311, h4315, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4315, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4302, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4319 | h4319
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4320 | h4320
                    · linarith only [h4245, h4247, h4320, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4320, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4323 | h4323
                    · linarith only [h4245, h4247, h4319, h4323, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4323, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4301, h4302, hc06, hlam, p0_1]
              · rcases h6emax with h4327 | h4327 | h4327 | h4327 | h4327 | h4327
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4328 | h4328
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4329 | h4329
                    · linarith only [h4247, h4329, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4327, h4328, h4329, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4332 | h4332
                    · linarith only [h4245, h4247, h4328, h4332, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4332, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4247, h4327, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4336 | h4336
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4337 | h4337
                    · linarith only [h4245, h4247, h4337, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4337, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4340 | h4340
                    · linarith only [h4245, h4247, h4336, h4340, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4340, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4245, h4327, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4344 | h4344
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4345 | h4345
                    · linarith only [h4245, h4247, h4345, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4344, h4345, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4348 | h4348
                    · linarith only [h4245, h4247, h4344, h4348, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4245, h4247, h4348, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4351 | h4351
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4352 | h4352
                    · linarith only [h4245, h4247, h4352, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4351, h4352, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4355 | h4355
                    · linarith only [h4245, h4247, h4355, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4245, h4247, h4355, hc01, hc16, hlam, hphi, p0_1]
          · linarith only [h4298, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h4359 | h4359
        · rcases p0_3 (m.d 3 6) (by simp) with h4360 | h4360
          · rcases p0_3 (m.d 4 6) (by simp) with h4361 | h4361
            · linarith only [h4361, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h4363 | h4363
              · rcases h6emax with h4364 | h4364 | h4364 | h4364 | h4364 | h4364
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4365 | h4365
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4366 | h4366
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4367 | h4367
                      · linarith only [h4245, h4359, h4365, h4366, h4367, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h4245, h4363, h4367, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4247, h4363, h4366, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4371 | h4371
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4372 | h4372
                      · linarith only [h4245, h4359, h4371, h4372, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4363, h4372, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4247, h4363, h4371, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4376 | h4376
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4377 | h4377
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4378 | h4378
                      · linarith only [h4245, h4359, h4378, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4363, h4378, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4364, h4376, h4377, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4382 | h4382
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4383 | h4383
                      · linarith only [h4245, h4359, h4382, h4383, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4363, h4383, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4364, h4382, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h4245, h4359, h4364, hc06, hlam, p0_1]
                · linarith only [h4245, h4364, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4389 | h4389
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4390 | h4390
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4391 | h4391
                      · linarith only [h4245, h4359, h4390, h4391, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4363, h4391, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4247, h4363, h4390, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4395 | h4395
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4396 | h4396
                      · linarith only [h4245, h4359, h4395, h4396, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4363, h4396, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4247, h4363, h4395, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h4245, h4363, h4364, hc06, hlam, p0_1]
              · rcases h6emax with h4401 | h4401 | h4401 | h4401 | h4401 | h4401
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4402 | h4402
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4403 | h4403
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4404 | h4404
                      · linarith only [h4245, h4359, h4403, h4404, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4404, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4247, h4402, h4403, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4408 | h4408
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4409 | h4409
                      · linarith only [h4245, h4359, h4409, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4409, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4247, h4408, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4413 | h4413
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4414 | h4414
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4415 | h4415
                      · linarith only [h4245, h4359, h4415, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4415, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4401, h4413, h4414, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4419 | h4419
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4420 | h4420
                      · linarith only [h4245, h4359, h4420, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4420, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4401, h4419, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h4245, h4359, h4401, hc06, hlam, p0_1]
                · linarith only [h4245, h4401, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4426 | h4426
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4427 | h4427
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4428 | h4428
                      · linarith only [h4245, h4359, h4427, h4428, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4428, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4247, h4426, h4427, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4432 | h4432
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4433 | h4433
                      · linarith only [h4245, h4359, h4433, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4433, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4247, h4432, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4437 | h4437
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4438 | h4438
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4439 | h4439
                      · linarith only [h4245, h4359, h4439, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4439, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4247, h4437, h4438, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4443 | h4443
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4444 | h4444
                      · linarith only [h4245, h4359, h4444, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4245, h4359, h4444, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4247, h4443, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h4360, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h4449 | h4449
          · rcases p0_3 (m.d 4 6) (by simp) with h4450 | h4450
            · linarith only [h4450, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h4452 | h4452
              · rcases h6emax with h4453 | h4453 | h4453 | h4453 | h4453 | h4453
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4454 | h4454
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4455 | h4455
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4456 | h4456
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4457 | h4457
                        · linarith only [h4245, h4455, h4457, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4452, h4457, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h4359, h4452, h4456, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4247, h4452, h4454, h4455, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4462 | h4462
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4463 | h4463
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4464 | h4464
                        · linarith only [h4245, h4462, h4464, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4452, h4464, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h4359, h4452, h4454, h4462, h4463, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h4247, h4452, h4462, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4469 | h4469
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4470 | h4470
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4471 | h4471
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4472 | h4472
                        · linarith only [h4245, h4472, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4472, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4452, h4471, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4453, h4469, h4470, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4477 | h4477
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4478 | h4478
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4479 | h4479
                        · linarith only [h4245, h4477, h4479, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4452, h4479, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h4359, h4452, h4469, h4478, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h4453, h4477, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4484 | h4484
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4485 | h4485
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4486 | h4486
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4487 | h4487
                        · linarith only [h4245, h4485, h4487, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4452, h4487, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h4245, h4452, h4453, h4485, h4486, hc02, hc16, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4247, h4452, h4485, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4492 | h4492
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4493 | h4493
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4494 | h4494
                        · linarith only [h4245, h4492, h4494, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4452, h4494, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h4453, h4484, h4492, h4493, hc16, hlam]
                    · linarith only [h4247, h4452, h4492, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h4245, h4453, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4500 | h4500
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4501 | h4501
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4502 | h4502
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4503 | h4503
                        · linarith only [h4245, h4501, h4503, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4503, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4452, h4502, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4247, h4452, h4500, h4501, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4508 | h4508
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4509 | h4509
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4510 | h4510
                        · linarith only [h4245, h4510, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4510, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4452, h4500, h4508, h4509, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h4247, h4452, h4508, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h4245, h4452, h4453, hc06, hlam, p0_1]
              · rcases h6emax with h4516 | h4516 | h4516 | h4516 | h4516 | h4516
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4517 | h4517
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4518 | h4518
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4519 | h4519
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4520 | h4520
                        · linarith only [h4245, h4518, h4520, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4520, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4519, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4247, h4517, h4518, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4525 | h4525
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4526 | h4526
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4527 | h4527
                        · linarith only [h4245, h4527, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4527, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4517, h4525, h4526, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h4247, h4525, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4532 | h4532
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4533 | h4533
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4534 | h4534
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4535 | h4535
                        · linarith only [h4245, h4535, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4535, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4534, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4516, h4532, h4533, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4540 | h4540
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4541 | h4541
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4542 | h4542
                        · linarith only [h4245, h4542, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4542, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4532, h4540, h4541, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h4516, h4540, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4547 | h4547
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4548 | h4548
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4549 | h4549
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4550 | h4550
                        · linarith only [h4245, h4550, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4550, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4516, h4549, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h4247, h4547, h4548, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4555 | h4555
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4556 | h4556
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4557 | h4557
                        · linarith only [h4245, h4557, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4557, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4516, h4547, h4556, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                    · linarith only [h4247, h4555, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h4245, h4516, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4563 | h4563
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4564 | h4564
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4565 | h4565
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4566 | h4566
                        · linarith only [h4245, h4564, h4566, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4566, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4565, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4247, h4564, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4571 | h4571
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4572 | h4572
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4573 | h4573
                        · linarith only [h4245, h4573, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4573, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4563, h4571, h4572, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h4247, h4571, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4578 | h4578
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4579 | h4579
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4580 | h4580
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4581 | h4581
                        · linarith only [h4245, h4581, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4581, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4580, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4247, h4578, h4579, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4586 | h4586
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4587 | h4587
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4588 | h4588
                        · linarith only [h4245, h4588, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4245, h4588, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4359, h4578, h4587, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h4247, h4586, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h4449, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h4594 | h4594
    · linarith only [h4594, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h4596 | h4596
      · rcases p0_3 (m.d 2 6) (by simp) with h4597 | h4597
        · rcases p0_3 (m.d 3 6) (by simp) with h4598 | h4598
          · rcases p0_3 (m.d 4 6) (by simp) with h4599 | h4599
            · rcases p0_3 (m.d 5 6) (by simp) with h4600 | h4600
              · linarith only [h4600, hlam, p0_0]
              · rcases h6emax with h4602 | h4602 | h4602 | h4602 | h4602 | h4602
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4603 | h4603
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4604 | h4604
                    · linarith only [h4596, h4604, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4602, h4603, h4604, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4607 | h4607
                    · linarith only [h4594, h4596, h4607, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4607, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4594, h4596, h4602, hc06, hlam, p0_1]
                · linarith only [h4594, h4597, h4602, hc06, hlam, p0_1]
                · linarith only [h4594, h4602, hc06, hlam, p0_1]
                · linarith only [h4594, h4599, h4602, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4614 | h4614
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4615 | h4615
                    · linarith only [h4594, h4596, h4615, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4614, h4615, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4618 | h4618
                    · linarith only [h4594, h4596, h4618, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4618, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h4621 | h4621
              · linarith only [h4621, hlam, p0_0]
              · rcases h6emax with h4623 | h4623 | h4623 | h4623 | h4623 | h4623
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4624 | h4624
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4625 | h4625
                    · linarith only [h4594, h4596, h4625, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4623, h4624, h4625, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4628 | h4628
                    · linarith only [h4594, h4596, h4628, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4628, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4594, h4596, h4623, hc06, hlam, p0_1]
                · linarith only [h4594, h4597, h4623, hc06, hlam, p0_1]
                · linarith only [h4594, h4623, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4634 | h4634
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4635 | h4635
                    · linarith only [h4594, h4596, h4635, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4635, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4638 | h4638
                    · linarith only [h4594, h4596, h4634, h4638, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4638, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4641 | h4641
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4642 | h4642
                    · linarith only [h4594, h4596, h4642, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4642, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4645 | h4645
                    · linarith only [h4594, h4596, h4641, h4645, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4645, hc01, hc16, hlam, hphi, p0_1]
          · linarith only [h4598, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h4649 | h4649
          · rcases p0_3 (m.d 4 6) (by simp) with h4650 | h4650
            · rcases p0_3 (m.d 5 6) (by simp) with h4651 | h4651
              · linarith only [h4651, hlam, p0_0]
              · rcases h6emax with h4653 | h4653 | h4653 | h4653 | h4653 | h4653
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4654 | h4654
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4655 | h4655
                    · linarith only [h4594, h4596, h4655, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4655, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4658 | h4658
                    · linarith only [h4594, h4596, h4654, h4658, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4658, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4594, h4596, h4653, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4662 | h4662
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4663 | h4663
                    · linarith only [h4594, h4596, h4663, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4663, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4666 | h4666
                    · linarith only [h4594, h4596, h4662, h4666, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4666, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4594, h4653, hc06, hlam, p0_1]
                · linarith only [h4594, h4650, h4653, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4671 | h4671
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4672 | h4672
                    · linarith only [h4594, h4596, h4672, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4672, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4675 | h4675
                    · linarith only [h4594, h4596, h4671, h4675, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4675, hc01, hc16, hlam, hphi, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h4678 | h4678
              · linarith only [h4678, hlam, p0_0]
              · rcases h6emax with h4680 | h4680 | h4680 | h4680 | h4680 | h4680
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4681 | h4681
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4682 | h4682
                    · linarith only [h4594, h4596, h4682, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4682, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4685 | h4685
                    · linarith only [h4594, h4596, h4681, h4685, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4685, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4594, h4596, h4680, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4689 | h4689
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4690 | h4690
                    · linarith only [h4594, h4596, h4690, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4690, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4693 | h4693
                    · linarith only [h4594, h4596, h4689, h4693, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4693, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4594, h4680, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4697 | h4697
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4698 | h4698
                    · linarith only [h4594, h4596, h4698, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4697, h4698, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4701 | h4701
                    · linarith only [h4594, h4596, h4697, h4701, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4701, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4704 | h4704
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4705 | h4705
                    · linarith only [h4594, h4596, h4705, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4594, h4596, h4705, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4708 | h4708
                    · linarith only [h4594, h4596, h4704, h4708, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4594, h4596, h4708, hc01, hc16, hlam, hphi, p0_1]
          · linarith only [h4649, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h4712 | h4712
        · rcases p0_3 (m.d 3 6) (by simp) with h4713 | h4713
          · rcases p0_3 (m.d 4 6) (by simp) with h4714 | h4714
            · rcases p0_3 (m.d 5 6) (by simp) with h4715 | h4715
              · linarith only [h4715, hlam, p0_0]
              · rcases h6emax with h4717 | h4717 | h4717 | h4717 | h4717 | h4717
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4718 | h4718
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4719 | h4719
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4720 | h4720
                      · linarith only [h4594, h4712, h4718, h4720, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h4594, h4712, h4720, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4714, h4719, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4724 | h4724
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4725 | h4725
                      · linarith only [h4594, h4712, h4725, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4725, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4714, h4724, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4729 | h4729
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4730 | h4730
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4731 | h4731
                      · linarith only [h4594, h4712, h4731, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4731, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4717, h4730, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4735 | h4735
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4736 | h4736
                      · linarith only [h4594, h4712, h4736, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4736, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4717, h4735, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h4594, h4712, h4717, hc06, hlam, p0_1]
                · linarith only [h4594, h4717, hc06, hlam, p0_1]
                · linarith only [h4594, h4714, h4717, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4743 | h4743
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4744 | h4744
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4745 | h4745
                      · linarith only [h4594, h4712, h4744, h4745, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4745, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4714, h4743, h4744, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4749 | h4749
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4750 | h4750
                      · linarith only [h4594, h4712, h4750, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4750, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4714, h4749, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h4754 | h4754
              · linarith only [h4754, hlam, p0_0]
              · rcases h6emax with h4756 | h4756 | h4756 | h4756 | h4756 | h4756
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4757 | h4757
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4758 | h4758
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4759 | h4759
                      · linarith only [h4594, h4712, h4758, h4759, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4759, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4758, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4763 | h4763
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4764 | h4764
                      · linarith only [h4594, h4712, h4764, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4764, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4763, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4768 | h4768
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4769 | h4769
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4770 | h4770
                      · linarith only [h4594, h4712, h4770, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4770, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4756, h4768, h4769, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4774 | h4774
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4775 | h4775
                      · linarith only [h4594, h4712, h4775, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4775, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4756, h4774, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h4594, h4712, h4756, hc06, hlam, p0_1]
                · linarith only [h4594, h4756, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4781 | h4781
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4782 | h4782
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4783 | h4783
                      · linarith only [h4594, h4712, h4782, h4783, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4783, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4781, h4782, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4787 | h4787
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4788 | h4788
                      · linarith only [h4594, h4712, h4788, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4788, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4787, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4792 | h4792
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4793 | h4793
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4794 | h4794
                      · linarith only [h4594, h4712, h4794, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4794, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4793, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4798 | h4798
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4799 | h4799
                      · linarith only [h4594, h4712, h4799, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h4594, h4712, h4799, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4596, h4798, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h4713, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h4804 | h4804
          · rcases p0_3 (m.d 4 6) (by simp) with h4805 | h4805
            · rcases p0_3 (m.d 5 6) (by simp) with h4806 | h4806
              · linarith only [h4806, hlam, p0_0]
              · rcases h6emax with h4808 | h4808 | h4808 | h4808 | h4808 | h4808
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4809 | h4809
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4810 | h4810
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4811 | h4811
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4812 | h4812
                        · linarith only [h4594, h4812, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4812, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4805, h4811, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h4596, h4805, h4809, h4810, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4817 | h4817
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4818 | h4818
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4819 | h4819
                        · linarith only [h4594, h4819, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4819, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4805, h4809, h4818, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h4596, h4805, h4817, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4824 | h4824
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4825 | h4825
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4826 | h4826
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4827 | h4827
                        · linarith only [h4594, h4827, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4827, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4805, h4826, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h4808, h4824, h4825, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4832 | h4832
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4833 | h4833
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4834 | h4834
                        · linarith only [h4594, h4834, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4834, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4805, h4824, h4832, h4833, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h4808, h4832, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4839 | h4839
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4840 | h4840
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4841 | h4841
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4842 | h4842
                        · linarith only [h4594, h4842, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4842, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4808, h4841, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h4596, h4805, h4840, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4847 | h4847
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4848 | h4848
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4849 | h4849
                        · linarith only [h4594, h4849, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4849, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4808, h4839, h4847, h4848, hc16, hlam]
                    · linarith only [h4596, h4805, h4847, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h4594, h4808, hc06, hlam, p0_1]
                · linarith only [h4594, h4805, h4808, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4856 | h4856
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4857 | h4857
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4858 | h4858
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4859 | h4859
                        · linarith only [h4594, h4857, h4859, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4859, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4805, h4858, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h4596, h4805, h4857, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4864 | h4864
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4865 | h4865
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4866 | h4866
                        · linarith only [h4594, h4866, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4866, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4805, h4856, h4864, h4865, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h4596, h4805, h4864, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases p0_3 (m.d 5 6) (by simp) with h4871 | h4871
              · linarith only [h4871, hlam, p0_0]
              · rcases h6emax with h4873 | h4873 | h4873 | h4873 | h4873 | h4873
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4874 | h4874
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4875 | h4875
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4876 | h4876
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4877 | h4877
                        · linarith only [h4594, h4877, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4877, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4876, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4596, h4874, h4875, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4882 | h4882
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4883 | h4883
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4884 | h4884
                        · linarith only [h4594, h4884, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4884, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4874, h4883, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h4596, h4882, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4889 | h4889
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4890 | h4890
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4891 | h4891
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4892 | h4892
                        · linarith only [h4594, h4892, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4892, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4891, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4873, h4890, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4897 | h4897
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4898 | h4898
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4899 | h4899
                        · linarith only [h4594, h4899, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4899, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4889, h4897, h4898, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h4873, h4897, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4904 | h4904
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4905 | h4905
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4906 | h4906
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4907 | h4907
                        · linarith only [h4594, h4907, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4907, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4873, h4906, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h4596, h4905, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4912 | h4912
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4913 | h4913
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4914 | h4914
                        · linarith only [h4594, h4914, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4914, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4873, h4904, h4912, h4913, hc16, hlam]
                    · linarith only [h4596, h4912, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · linarith only [h4594, h4873, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4920 | h4920
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4921 | h4921
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4922 | h4922
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4923 | h4923
                        · linarith only [h4594, h4921, h4923, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4923, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4922, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4596, h4920, h4921, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4928 | h4928
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4929 | h4929
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4930 | h4930
                        · linarith only [h4594, h4930, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4930, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4920, h4928, h4929, hc16, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1]
                    · linarith only [h4596, h4928, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4935 | h4935
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4936 | h4936
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4937 | h4937
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4938 | h4938
                        · linarith only [h4594, h4938, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4938, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4937, hc02, hc36, hlam, hphi, ht23, p0_1]
                    · linarith only [h4596, h4935, h4936, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4943 | h4943
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h4944 | h4944
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h4945 | h4945
                        · linarith only [h4594, h4945, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h4594, h4945, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h4712, h4935, h4944, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h4596, h4943, hc01, hc36, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h4804, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h4951 | h4951
    · linarith only [h4951, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h4953 | h4953
      · rcases p0_3 (m.d 2 6) (by simp) with h4954 | h4954
        · rcases p0_3 (m.d 3 6) (by simp) with h4955 | h4955
          · rcases p0_3 (m.d 4 6) (by simp) with h4956 | h4956
            · rcases p0_3 (m.d 5 6) (by simp) with h4957 | h4957
              · rcases h6emax with h4958 | h4958 | h4958 | h4958 | h4958 | h4958
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4959 | h4959
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4960 | h4960
                    · linarith only [h4953, h4960, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h4960, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4963 | h4963
                    · linarith only [h4953, h4963, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h4963, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h4958, hc06, hlam, p0_1]
                · linarith only [h4954, h4958, hc06, hlam, p0_1]
                · linarith only [h4955, h4958, hc06, hlam, p0_1]
                · linarith only [h4958, hc06, hlam, p0_1]
                · linarith only [h4957, h4958, hc06, hlam, p0_1]
              · rcases h6emax with h4971 | h4971 | h4971 | h4971 | h4971 | h4971
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4972 | h4972
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4973 | h4973
                    · linarith only [h4953, h4973, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h4973, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4976 | h4976
                    · linarith only [h4953, h4972, h4976, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h4976, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h4971, hc06, hlam, p0_1]
                · linarith only [h4954, h4971, hc06, hlam, p0_1]
                · linarith only [h4955, h4971, hc06, hlam, p0_1]
                · linarith only [h4971, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4983 | h4983
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4984 | h4984
                    · linarith only [h4953, h4984, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h4983, h4984, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4987 | h4987
                    · linarith only [h4953, h4987, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h4987, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h4956, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h4991 | h4991
            · rcases p0_3 (m.d 5 6) (by simp) with h4992 | h4992
              · rcases h6emax with h4993 | h4993 | h4993 | h4993 | h4993 | h4993
                · rcases m.htr 0 1 2 (by decide) (by decide) with h4994 | h4994
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4995 | h4995
                    · linarith only [h4953, h4995, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h4995, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h4998 | h4998
                    · linarith only [h4953, h4994, h4998, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h4998, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h4993, hc06, hlam, p0_1]
                · linarith only [h4954, h4993, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5003 | h5003
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5004 | h5004
                    · linarith only [h4953, h5004, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5003, h5004, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5007 | h5007
                    · linarith only [h4953, h5007, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5007, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4993, hc06, hlam, p0_1]
                · linarith only [h4992, h4993, hc06, hlam, p0_1]
              · rcases h6emax with h5012 | h5012 | h5012 | h5012 | h5012 | h5012
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5013 | h5013
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5014 | h5014
                    · linarith only [h4953, h5014, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5014, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5017 | h5017
                    · linarith only [h4953, h5013, h5017, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5017, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h5012, hc06, hlam, p0_1]
                · linarith only [h4954, h5012, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5022 | h5022
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5023 | h5023
                    · linarith only [h4953, h5023, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5023, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5026 | h5026
                    · linarith only [h4953, h5022, h5026, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5026, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5012, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5030 | h5030
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5031 | h5031
                    · linarith only [h4953, h5031, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5030, h5031, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5034 | h5034
                    · linarith only [h4953, h5034, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5034, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h4991, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h5038 | h5038
          · rcases p0_3 (m.d 4 6) (by simp) with h5039 | h5039
            · rcases p0_3 (m.d 5 6) (by simp) with h5040 | h5040
              · rcases h6emax with h5041 | h5041 | h5041 | h5041 | h5041 | h5041
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5042 | h5042
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5043 | h5043
                    · linarith only [h4953, h5043, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5043, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5046 | h5046
                    · linarith only [h4953, h5042, h5046, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5046, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h5041, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5050 | h5050
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5051 | h5051
                    · linarith only [h4953, h5051, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5051, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5054 | h5054
                    · linarith only [h4953, h5054, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5054, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5038, h5041, hc06, hlam, p0_1]
                · linarith only [h5041, hc06, hlam, p0_1]
                · linarith only [h5040, h5041, hc06, hlam, p0_1]
              · rcases h6emax with h5060 | h5060 | h5060 | h5060 | h5060 | h5060
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5061 | h5061
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5062 | h5062
                    · linarith only [h4953, h5062, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5060, h5061, h5062, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5065 | h5065
                    · linarith only [h4953, h5061, h5065, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5065, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h5060, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5069 | h5069
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5070 | h5070
                    · linarith only [h4953, h5070, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5069, h5070, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5073 | h5073
                    · linarith only [h4953, h5073, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5073, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5038, h5060, hc06, hlam, p0_1]
                · linarith only [h5060, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5078 | h5078
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5079 | h5079
                    · linarith only [h4953, h5079, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5079, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5082 | h5082
                    · linarith only [h4953, h5078, h5082, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5082, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h5039, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h5086 | h5086
            · rcases p0_3 (m.d 5 6) (by simp) with h5087 | h5087
              · rcases h6emax with h5088 | h5088 | h5088 | h5088 | h5088 | h5088
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5089 | h5089
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5090 | h5090
                    · linarith only [h4953, h5090, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5090, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5093 | h5093
                    · linarith only [h4953, h5089, h5093, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5093, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h5088, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5097 | h5097
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5098 | h5098
                    · linarith only [h4953, h5098, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5098, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5101 | h5101
                    · linarith only [h4953, h5097, h5101, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5101, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5104 | h5104
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5105 | h5105
                    · linarith only [h4953, h5105, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5105, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5108 | h5108
                    · linarith only [h4953, h5104, h5108, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5108, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5088, hc06, hlam, p0_1]
                · linarith only [h5087, h5088, hc06, hlam, p0_1]
              · rcases h6emax with h5113 | h5113 | h5113 | h5113 | h5113 | h5113
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5114 | h5114
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5115 | h5115
                    · linarith only [h4953, h5115, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5115, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5118 | h5118
                    · linarith only [h4953, h5114, h5118, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5118, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h4953, h5113, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5122 | h5122
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5123 | h5123
                    · linarith only [h4953, h5123, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5122, h5123, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5126 | h5126
                    · linarith only [h4953, h5122, h5126, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5126, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5129 | h5129
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5130 | h5130
                    · linarith only [h4953, h5130, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5130, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5133 | h5133
                    · linarith only [h4953, h5129, h5133, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h4953, h5133, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5113, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5137 | h5137
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5138 | h5138
                    · linarith only [h4953, h5138, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5137, h5138, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5141 | h5141
                    · linarith only [h4953, h5141, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h4953, h5141, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h5086, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h5145 | h5145
        · rcases p0_3 (m.d 3 6) (by simp) with h5146 | h5146
          · rcases p0_3 (m.d 4 6) (by simp) with h5147 | h5147
            · rcases p0_3 (m.d 5 6) (by simp) with h5148 | h5148
              · rcases h6emax with h5149 | h5149 | h5149 | h5149 | h5149 | h5149
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5150 | h5150
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5151 | h5151
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5152 | h5152
                      · linarith only [h5145, h5150, h5151, h5152, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h5148, h5152, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5151, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5156 | h5156
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5157 | h5157
                      · linarith only [h5145, h5156, h5157, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5148, h5157, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5156, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5161 | h5161
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5162 | h5162
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5163 | h5163
                      · linarith only [h5145, h5162, h5163, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5148, h5163, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5162, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5167 | h5167
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5168 | h5168
                      · linarith only [h5145, h5167, h5168, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5148, h5168, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5167, hlam]
                · linarith only [h5145, h5149, hc06, hlam, p0_1]
                · linarith only [h5146, h5149, hc06, hlam, p0_1]
                · linarith only [h5149, hc06, hlam, p0_1]
                · linarith only [h5148, h5149, hc06, hlam, p0_1]
              · rcases h6emax with h5176 | h5176 | h5176 | h5176 | h5176 | h5176
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5177 | h5177
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5178 | h5178
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5179 | h5179
                      · linarith only [h5145, h5178, h5179, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5179, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5178, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5183 | h5183
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5184 | h5184
                      · linarith only [h5145, h5184, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5177, h5184, hc01, hc26, hlam, hphi, ht12, p0_1]
                    · linarith only [h4953, h5183, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5188 | h5188
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5189 | h5189
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5190 | h5190
                      · linarith only [h5145, h5190, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5190, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5189, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5194 | h5194
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5195 | h5195
                      · linarith only [h5145, h5195, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5195, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5194, hlam]
                · linarith only [h5145, h5176, hc06, hlam, p0_1]
                · linarith only [h5146, h5176, hc06, hlam, p0_1]
                · linarith only [h5176, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5202 | h5202
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5203 | h5203
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5204 | h5204
                      · linarith only [h5145, h5203, h5204, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5204, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5203, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5208 | h5208
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5209 | h5209
                      · linarith only [h5145, h5209, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5209, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5208, hlam]
            · linarith only [h5147, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h5214 | h5214
            · rcases p0_3 (m.d 5 6) (by simp) with h5215 | h5215
              · rcases h6emax with h5216 | h5216 | h5216 | h5216 | h5216 | h5216
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5217 | h5217
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5218 | h5218
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5219 | h5219
                      · linarith only [h5145, h5218, h5219, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5215, h5219, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5218, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5223 | h5223
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5224 | h5224
                      · linarith only [h5145, h5223, h5224, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5215, h5224, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5223, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5228 | h5228
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5229 | h5229
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5230 | h5230
                      · linarith only [h5145, h5229, h5230, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5215, h5230, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5229, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5234 | h5234
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5235 | h5235
                      · linarith only [h5145, h5234, h5235, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5215, h5228, h5235, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5234, hlam]
                · linarith only [h5145, h5216, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5240 | h5240
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5241 | h5241
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5242 | h5242
                      · linarith only [h5145, h5241, h5242, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5215, h5242, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5241, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5246 | h5246
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5247 | h5247
                      · linarith only [h5145, h5246, h5247, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5215, h5247, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h4953, h5246, hlam]
                · linarith only [h5216, hc06, hlam, p0_1]
                · linarith only [h5215, h5216, hc06, hlam, p0_1]
              · rcases h6emax with h5253 | h5253 | h5253 | h5253 | h5253 | h5253
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5254 | h5254
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5255 | h5255
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5256 | h5256
                      · linarith only [h5145, h5255, h5256, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5256, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5255, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5260 | h5260
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5261 | h5261
                      · linarith only [h5145, h5261, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5254, h5261, hc01, hc26, hlam, hphi, ht12, p0_1]
                    · linarith only [h4953, h5260, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5265 | h5265
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5266 | h5266
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5267 | h5267
                      · linarith only [h5145, h5267, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5267, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5266, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5271 | h5271
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5272 | h5272
                      · linarith only [h5145, h5272, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5272, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5271, hlam]
                · linarith only [h5145, h5253, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5277 | h5277
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5278 | h5278
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5279 | h5279
                      · linarith only [h5145, h5278, h5279, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5279, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5278, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5283 | h5283
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5284 | h5284
                      · linarith only [h5145, h5284, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5284, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5283, hlam]
                · linarith only [h5253, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5289 | h5289
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5290 | h5290
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5291 | h5291
                      · linarith only [h5145, h5290, h5291, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5291, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5290, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5295 | h5295
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5296 | h5296
                      · linarith only [h5145, h5296, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h5145, h5296, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h4953, h5295, hlam]
            · linarith only [h5214, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h5301 | h5301
          · rcases p0_3 (m.d 4 6) (by simp) with h5302 | h5302
            · rcases p0_3 (m.d 5 6) (by simp) with h5303 | h5303
              · rcases h6emax with h5304 | h5304 | h5304 | h5304 | h5304 | h5304
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5305 | h5305
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5306 | h5306
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5307 | h5307
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5308 | h5308
                        · linarith only [h5301, h5306, h5308, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5303, h5308, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h5145, h5307, hlam]
                    · linarith only [h4953, h5306, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5313 | h5313
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5314 | h5314
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5315 | h5315
                        · linarith only [h5301, h5313, h5315, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5303, h5315, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h5145, h5314, hlam]
                    · linarith only [h4953, h5313, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5320 | h5320
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5321 | h5321
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5322 | h5322
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5323 | h5323
                        · linarith only [h5301, h5321, h5323, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5303, h5323, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h5145, h5322, hlam]
                    · linarith only [h4953, h5321, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5328 | h5328
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5329 | h5329
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5330 | h5330
                        · linarith only [h5301, h5328, h5330, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5303, h5330, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h5145, h5329, hlam]
                    · linarith only [h4953, h5328, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5335 | h5335
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5336 | h5336
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5337 | h5337
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5338 | h5338
                        · linarith only [h5301, h5336, h5338, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5303, h5338, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h5145, h5337, hlam]
                    · linarith only [h4953, h5336, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5343 | h5343
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5344 | h5344
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5345 | h5345
                        · linarith only [h5301, h5343, h5345, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5303, h5345, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h5145, h5344, hlam]
                    · linarith only [h4953, h5343, hlam]
                · linarith only [h5301, h5304, hc06, hlam, p0_1]
                · linarith only [h5304, hc06, hlam, p0_1]
                · linarith only [h5303, h5304, hc06, hlam, p0_1]
              · rcases h6emax with h5353 | h5353 | h5353 | h5353 | h5353 | h5353
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5354 | h5354
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5355 | h5355
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5356 | h5356
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5357 | h5357
                        · linarith only [h5301, h5355, h5357, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5357, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5356, hlam]
                    · linarith only [h4953, h5355, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5362 | h5362
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5363 | h5363
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5364 | h5364
                        · linarith only [h5301, h5364, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5364, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5363, hlam]
                    · linarith only [h4953, h5362, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5369 | h5369
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5370 | h5370
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5371 | h5371
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5372 | h5372
                        · linarith only [h5301, h5372, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5372, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5371, hlam]
                    · linarith only [h4953, h5370, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5377 | h5377
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5378 | h5378
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5379 | h5379
                        · linarith only [h5301, h5379, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5379, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5378, hlam]
                    · linarith only [h4953, h5377, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5384 | h5384
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5385 | h5385
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5386 | h5386
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5387 | h5387
                        · linarith only [h5301, h5387, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5387, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5386, hlam]
                    · linarith only [h4953, h5385, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5392 | h5392
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5393 | h5393
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5394 | h5394
                        · linarith only [h5301, h5394, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5394, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5393, hlam]
                    · linarith only [h4953, h5392, hlam]
                · linarith only [h5301, h5353, hc06, hlam, p0_1]
                · linarith only [h5353, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5401 | h5401
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5402 | h5402
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5403 | h5403
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5404 | h5404
                        · linarith only [h5301, h5402, h5404, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5404, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5403, hlam]
                    · linarith only [h4953, h5402, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5409 | h5409
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5410 | h5410
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5411 | h5411
                        · linarith only [h5301, h5411, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h5301, h5411, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h5145, h5410, hlam]
                    · linarith only [h4953, h5409, hlam]
            · linarith only [h5302, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h5417 | h5417
            · rcases p0_3 (m.d 5 6) (by simp) with h5418 | h5418
              · rcases h6emax with h5419 | h5419 | h5419 | h5419 | h5419 | h5419
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5420 | h5420
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5421 | h5421
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5422 | h5422
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5423 | h5423
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5424 | h5424
                          · linarith only [h5424, hlam, p0_0]
                          · linarith only [h5418, h5424, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5423, hlam]
                      · linarith only [h5145, h5422, hlam]
                    · linarith only [h4953, h5421, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5430 | h5430
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5431 | h5431
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5432 | h5432
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5433 | h5433
                          · linarith only [h5433, hlam, p0_0]
                          · linarith only [h5418, h5433, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5432, hlam]
                      · linarith only [h5145, h5431, hlam]
                    · linarith only [h4953, h5430, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5439 | h5439
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5440 | h5440
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5441 | h5441
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5442 | h5442
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5443 | h5443
                          · linarith only [h5443, hlam, p0_0]
                          · linarith only [h5418, h5443, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5442, hlam]
                      · linarith only [h5145, h5441, hlam]
                    · linarith only [h4953, h5440, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5449 | h5449
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5450 | h5450
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5451 | h5451
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5452 | h5452
                          · linarith only [h5452, hlam, p0_0]
                          · linarith only [h5418, h5452, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5451, hlam]
                      · linarith only [h5145, h5450, hlam]
                    · linarith only [h4953, h5449, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5458 | h5458
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5459 | h5459
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5460 | h5460
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5461 | h5461
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5462 | h5462
                          · linarith only [h5462, hlam, p0_0]
                          · linarith only [h5418, h5462, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5461, hlam]
                      · linarith only [h5145, h5460, hlam]
                    · linarith only [h4953, h5459, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5468 | h5468
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5469 | h5469
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5470 | h5470
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5471 | h5471
                          · linarith only [h5471, hlam, p0_0]
                          · linarith only [h5418, h5471, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5470, hlam]
                      · linarith only [h5145, h5469, hlam]
                    · linarith only [h4953, h5468, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5477 | h5477
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5478 | h5478
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5479 | h5479
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5480 | h5480
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5481 | h5481
                          · linarith only [h5481, hlam, p0_0]
                          · linarith only [h5418, h5481, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5480, hlam]
                      · linarith only [h5145, h5479, hlam]
                    · linarith only [h4953, h5478, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5487 | h5487
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5488 | h5488
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5489 | h5489
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5490 | h5490
                          · linarith only [h5490, hlam, p0_0]
                          · linarith only [h5418, h5490, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h5301, h5489, hlam]
                      · linarith only [h5145, h5488, hlam]
                    · linarith only [h4953, h5487, hlam]
                · linarith only [h5419, hc06, hlam, p0_1]
                · linarith only [h5418, h5419, hc06, hlam, p0_1]
              · rcases h6emax with h5498 | h5498 | h5498 | h5498 | h5498 | h5498
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5499 | h5499
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5500 | h5500
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5501 | h5501
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5502 | h5502
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5503 | h5503
                          · linarith only [h5503, hlam, p0_0]
                          · linarith only [h5503, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5502, hlam]
                      · linarith only [h5145, h5501, hlam]
                    · linarith only [h4953, h5500, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5509 | h5509
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5510 | h5510
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5511 | h5511
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5512 | h5512
                          · linarith only [h5512, hlam, p0_0]
                          · linarith only [h5512, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5511, hlam]
                      · linarith only [h5145, h5510, hlam]
                    · linarith only [h4953, h5509, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5518 | h5518
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5519 | h5519
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5520 | h5520
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5521 | h5521
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5522 | h5522
                          · linarith only [h5522, hlam, p0_0]
                          · linarith only [h5522, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5521, hlam]
                      · linarith only [h5145, h5520, hlam]
                    · linarith only [h4953, h5519, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5528 | h5528
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5529 | h5529
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5530 | h5530
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5531 | h5531
                          · linarith only [h5531, hlam, p0_0]
                          · linarith only [h5531, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5530, hlam]
                      · linarith only [h5145, h5529, hlam]
                    · linarith only [h4953, h5528, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5537 | h5537
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5538 | h5538
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5539 | h5539
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5540 | h5540
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5541 | h5541
                          · linarith only [h5541, hlam, p0_0]
                          · linarith only [h5541, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5540, hlam]
                      · linarith only [h5145, h5539, hlam]
                    · linarith only [h4953, h5538, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5547 | h5547
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5548 | h5548
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5549 | h5549
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5550 | h5550
                          · linarith only [h5550, hlam, p0_0]
                          · linarith only [h5550, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5549, hlam]
                      · linarith only [h5145, h5548, hlam]
                    · linarith only [h4953, h5547, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5556 | h5556
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5557 | h5557
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5558 | h5558
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5559 | h5559
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5560 | h5560
                          · linarith only [h5560, hlam, p0_0]
                          · linarith only [h5560, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5559, hlam]
                      · linarith only [h5145, h5558, hlam]
                    · linarith only [h4953, h5557, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5566 | h5566
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5567 | h5567
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5568 | h5568
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5569 | h5569
                          · linarith only [h5569, hlam, p0_0]
                          · linarith only [h5569, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5568, hlam]
                      · linarith only [h5145, h5567, hlam]
                    · linarith only [h4953, h5566, hlam]
                · linarith only [h5498, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5576 | h5576
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5577 | h5577
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5578 | h5578
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5579 | h5579
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5580 | h5580
                          · linarith only [h5580, hlam, p0_0]
                          · linarith only [h5580, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5579, hlam]
                      · linarith only [h5145, h5578, hlam]
                    · linarith only [h4953, h5577, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5586 | h5586
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5587 | h5587
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h5588 | h5588
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h5589 | h5589
                          · linarith only [h5589, hlam, p0_0]
                          · linarith only [h5589, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h5301, h5588, hlam]
                      · linarith only [h5145, h5587, hlam]
                    · linarith only [h4953, h5586, hlam]
            · linarith only [h5417, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h5596 | h5596
    · linarith only [h5596, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h5598 | h5598
      · linarith only [h5598, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h5600 | h5600
        · rcases p0_3 (m.d 3 6) (by simp) with h5601 | h5601
          · rcases p0_3 (m.d 4 6) (by simp) with h5602 | h5602
            · rcases p0_3 (m.d 5 6) (by simp) with h5603 | h5603
              · rcases h6emax with h5604 | h5604 | h5604 | h5604 | h5604 | h5604
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5605 | h5605
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5606 | h5606
                    · linarith only [h5596, h5606, hlam]
                    · linarith only [h5603, h5606, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5609 | h5609
                    · linarith only [h5596, h5609, hlam]
                    · linarith only [h5603, h5609, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5612 | h5612
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5613 | h5613
                    · linarith only [h5596, h5613, hlam]
                    · linarith only [h5603, h5612, h5613, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5616 | h5616
                    · linarith only [h5596, h5616, hlam]
                    · linarith only [h5603, h5616, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h5600, h5604, hc16, hlam, p0_1]
                · linarith only [h5601, h5604, hc16, hlam, p0_1]
                · linarith only [h5604, hc16, hlam, p0_1]
                · linarith only [h5603, h5604, hc16, hlam, p0_1]
              · rcases h6emax with h5623 | h5623 | h5623 | h5623 | h5623 | h5623
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5624 | h5624
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5625 | h5625
                    · linarith only [h5596, h5625, hlam]
                    · linarith only [h5600, h5624, h5625, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5628 | h5628
                    · linarith only [h5596, h5628, hlam]
                    · linarith only [h5628, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5631 | h5631
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5632 | h5632
                    · linarith only [h5596, h5632, hlam]
                    · linarith only [h5631, h5632, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5635 | h5635
                    · linarith only [h5596, h5635, hlam]
                    · linarith only [h5635, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h5600, h5623, hc16, hlam, p0_1]
                · linarith only [h5601, h5623, hc16, hlam, p0_1]
                · linarith only [h5623, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5641 | h5641
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5642 | h5642
                    · linarith only [h5596, h5642, hlam]
                    · linarith only [h5600, h5641, h5642, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5645 | h5645
                    · linarith only [h5596, h5645, hlam]
                    · linarith only [h5645, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h5602, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h5649 | h5649
            · rcases p0_3 (m.d 5 6) (by simp) with h5650 | h5650
              · rcases h6emax with h5651 | h5651 | h5651 | h5651 | h5651 | h5651
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5652 | h5652
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5653 | h5653
                    · linarith only [h5596, h5653, hlam]
                    · linarith only [h5650, h5653, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5656 | h5656
                    · linarith only [h5596, h5656, hlam]
                    · linarith only [h5650, h5656, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5659 | h5659
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5660 | h5660
                    · linarith only [h5596, h5660, hlam]
                    · linarith only [h5650, h5659, h5660, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5663 | h5663
                    · linarith only [h5596, h5663, hlam]
                    · linarith only [h5650, h5663, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h5600, h5651, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5667 | h5667
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5668 | h5668
                    · linarith only [h5596, h5668, hlam]
                    · linarith only [h5650, h5667, h5668, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5671 | h5671
                    · linarith only [h5596, h5671, hlam]
                    · linarith only [h5650, h5671, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h5651, hc16, hlam, p0_1]
                · linarith only [h5650, h5651, hc16, hlam, p0_1]
              · rcases h6emax with h5676 | h5676 | h5676 | h5676 | h5676 | h5676
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5677 | h5677
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5678 | h5678
                    · linarith only [h5596, h5678, hlam]
                    · linarith only [h5600, h5677, h5678, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5681 | h5681
                    · linarith only [h5596, h5681, hlam]
                    · linarith only [h5681, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5684 | h5684
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5685 | h5685
                    · linarith only [h5596, h5685, hlam]
                    · linarith only [h5684, h5685, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5688 | h5688
                    · linarith only [h5596, h5688, hlam]
                    · linarith only [h5688, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h5600, h5676, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5692 | h5692
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5693 | h5693
                    · linarith only [h5596, h5693, hlam]
                    · linarith only [h5600, h5692, h5693, hc12, hc26, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5696 | h5696
                    · linarith only [h5596, h5696, hlam]
                    · linarith only [h5696, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h5676, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5700 | h5700
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5701 | h5701
                    · linarith only [h5596, h5701, hlam]
                    · linarith only [h5700, h5701, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5704 | h5704
                    · linarith only [h5596, h5704, hlam]
                    · linarith only [h5704, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h5649, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h5708 | h5708
          · rcases p0_3 (m.d 4 6) (by simp) with h5709 | h5709
            · rcases p0_3 (m.d 5 6) (by simp) with h5710 | h5710
              · rcases h6emax with h5711 | h5711 | h5711 | h5711 | h5711 | h5711
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5712 | h5712
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5713 | h5713
                    · linarith only [h5596, h5713, hlam]
                    · linarith only [h5710, h5712, h5713, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5716 | h5716
                    · linarith only [h5596, h5716, hlam]
                    · linarith only [h5710, h5716, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5719 | h5719
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5720 | h5720
                    · linarith only [h5596, h5720, hlam]
                    · linarith only [h5710, h5719, h5720, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5723 | h5723
                    · linarith only [h5596, h5723, hlam]
                    · linarith only [h5710, h5723, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5726 | h5726
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5727 | h5727
                    · linarith only [h5596, h5727, hlam]
                    · linarith only [h5710, h5726, h5727, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5730 | h5730
                    · linarith only [h5596, h5730, hlam]
                    · linarith only [h5710, h5730, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h5708, h5711, hc16, hlam, p0_1]
                · linarith only [h5711, hc16, hlam, p0_1]
                · linarith only [h5710, h5711, hc16, hlam, p0_1]
              · rcases h6emax with h5736 | h5736 | h5736 | h5736 | h5736 | h5736
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5737 | h5737
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5738 | h5738
                    · linarith only [h5596, h5738, hlam]
                    · linarith only [h5708, h5737, h5738, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5741 | h5741
                    · linarith only [h5596, h5741, hlam]
                    · linarith only [h5741, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5744 | h5744
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5745 | h5745
                    · linarith only [h5596, h5745, hlam]
                    · linarith only [h5745, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5748 | h5748
                    · linarith only [h5596, h5748, hlam]
                    · linarith only [h5748, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5751 | h5751
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5752 | h5752
                    · linarith only [h5596, h5752, hlam]
                    · linarith only [h5751, h5752, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5755 | h5755
                    · linarith only [h5596, h5755, hlam]
                    · linarith only [h5755, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h5708, h5736, hc16, hlam, p0_1]
                · linarith only [h5736, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5760 | h5760
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5761 | h5761
                    · linarith only [h5596, h5761, hlam]
                    · linarith only [h5708, h5760, h5761, hc12, hc36, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5764 | h5764
                    · linarith only [h5596, h5764, hlam]
                    · linarith only [h5764, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h5709, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h5768 | h5768
            · rcases p0_3 (m.d 5 6) (by simp) with h5769 | h5769
              · rcases h6emax with h5770 | h5770 | h5770 | h5770 | h5770 | h5770
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5771 | h5771
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5772 | h5772
                    · linarith only [h5596, h5772, hlam]
                    · linarith only [h5769, h5772, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5775 | h5775
                    · linarith only [h5596, h5775, hlam]
                    · linarith only [h5769, h5775, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5778 | h5778
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5779 | h5779
                    · linarith only [h5596, h5779, hlam]
                    · linarith only [h5769, h5779, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5782 | h5782
                    · linarith only [h5596, h5782, hlam]
                    · linarith only [h5769, h5782, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5785 | h5785
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5786 | h5786
                    · linarith only [h5596, h5786, hlam]
                    · linarith only [h5769, h5786, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5789 | h5789
                    · linarith only [h5596, h5789, hlam]
                    · linarith only [h5769, h5789, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5792 | h5792
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5793 | h5793
                    · linarith only [h5596, h5793, hlam]
                    · linarith only [h5769, h5793, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5796 | h5796
                    · linarith only [h5596, h5796, hlam]
                    · linarith only [h5769, h5796, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h5770, hc16, hlam, p0_1]
                · linarith only [h5769, h5770, hc16, hlam, p0_1]
              · rcases h6emax with h5801 | h5801 | h5801 | h5801 | h5801 | h5801
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5802 | h5802
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5803 | h5803
                    · linarith only [h5596, h5803, hlam]
                    · linarith only [h5803, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5806 | h5806
                    · linarith only [h5596, h5806, hlam]
                    · linarith only [h5806, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5809 | h5809
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5810 | h5810
                    · linarith only [h5596, h5810, hlam]
                    · linarith only [h5809, h5810, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5813 | h5813
                    · linarith only [h5596, h5813, hlam]
                    · linarith only [h5813, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5816 | h5816
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5817 | h5817
                    · linarith only [h5596, h5817, hlam]
                    · linarith only [h5816, h5817, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5820 | h5820
                    · linarith only [h5596, h5820, hlam]
                    · linarith only [h5820, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5823 | h5823
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5824 | h5824
                    · linarith only [h5596, h5824, hlam]
                    · linarith only [h5823, h5824, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5827 | h5827
                    · linarith only [h5596, h5827, hlam]
                    · linarith only [h5827, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h5801, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5831 | h5831
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5832 | h5832
                    · linarith only [h5596, h5832, hlam]
                    · linarith only [h5831, h5832, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5835 | h5835
                    · linarith only [h5596, h5835, hlam]
                    · linarith only [h5835, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h5768, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h5839 | h5839
    · linarith only [h5839, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h5841 | h5841
      · rcases p0_3 (m.d 2 6) (by simp) with h5842 | h5842
        · linarith only [h5842, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h5844 | h5844
          · rcases p0_3 (m.d 4 6) (by simp) with h5845 | h5845
            · rcases p0_3 (m.d 5 6) (by simp) with h5846 | h5846
              · rcases h6emax with h5847 | h5847 | h5847 | h5847 | h5847 | h5847
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5848 | h5848
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5849 | h5849
                    · linarith only [h5841, h5849, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5849, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5852 | h5852
                    · linarith only [h5839, h5841, h5852, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5852, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5841, h5847, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5856 | h5856
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5857 | h5857
                    · linarith only [h5839, h5841, h5857, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5857, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5860 | h5860
                    · linarith only [h5839, h5841, h5856, h5860, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5860, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5844, h5847, hc06, hlam, p0_1]
                · linarith only [h5839, h5847, hc06, hlam, p0_1]
                · linarith only [h5839, h5846, h5847, hc06, hlam, p0_1]
              · rcases h6emax with h5866 | h5866 | h5866 | h5866 | h5866 | h5866
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5867 | h5867
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5868 | h5868
                    · linarith only [h5841, h5868, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5868, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5871 | h5871
                    · linarith only [h5839, h5841, h5867, h5871, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5871, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5841, h5866, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5875 | h5875
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5876 | h5876
                    · linarith only [h5839, h5841, h5876, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5876, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5879 | h5879
                    · linarith only [h5839, h5841, h5875, h5879, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5879, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5844, h5866, hc06, hlam, p0_1]
                · linarith only [h5839, h5866, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5884 | h5884
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5885 | h5885
                    · linarith only [h5839, h5841, h5885, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5885, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5888 | h5888
                    · linarith only [h5839, h5841, h5884, h5888, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5888, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h5845, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h5892 | h5892
            · rcases p0_3 (m.d 5 6) (by simp) with h5893 | h5893
              · rcases h6emax with h5894 | h5894 | h5894 | h5894 | h5894 | h5894
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5895 | h5895
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5896 | h5896
                    · linarith only [h5839, h5841, h5896, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5896, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5899 | h5899
                    · linarith only [h5839, h5841, h5895, h5899, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5899, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5841, h5894, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5903 | h5903
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5904 | h5904
                    · linarith only [h5839, h5841, h5904, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5903, h5904, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5907 | h5907
                    · linarith only [h5839, h5841, h5903, h5907, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5907, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5910 | h5910
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5911 | h5911
                    · linarith only [h5839, h5841, h5911, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5911, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5914 | h5914
                    · linarith only [h5839, h5841, h5910, h5914, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5914, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5894, hc06, hlam, p0_1]
                · linarith only [h5839, h5893, h5894, hc06, hlam, p0_1]
              · rcases h6emax with h5919 | h5919 | h5919 | h5919 | h5919 | h5919
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5920 | h5920
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5921 | h5921
                    · linarith only [h5839, h5841, h5921, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5919, h5920, h5921, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5924 | h5924
                    · linarith only [h5839, h5841, h5920, h5924, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5924, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5841, h5919, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5928 | h5928
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5929 | h5929
                    · linarith only [h5839, h5841, h5929, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5929, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5932 | h5932
                    · linarith only [h5839, h5841, h5928, h5932, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5932, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5935 | h5935
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5936 | h5936
                    · linarith only [h5839, h5841, h5936, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5936, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5939 | h5939
                    · linarith only [h5839, h5841, h5935, h5939, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5939, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h5839, h5919, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5943 | h5943
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5944 | h5944
                    · linarith only [h5839, h5841, h5944, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h5839, h5841, h5943, h5944, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5947 | h5947
                    · linarith only [h5839, h5841, h5943, h5947, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h5839, h5841, h5947, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h5892, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h5951 | h5951
        · linarith only [h5951, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h5953 | h5953
          · rcases p0_3 (m.d 4 6) (by simp) with h5954 | h5954
            · rcases p0_3 (m.d 5 6) (by simp) with h5955 | h5955
              · rcases h6emax with h5956 | h5956 | h5956 | h5956 | h5956 | h5956
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5957 | h5957
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5958 | h5958
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5959 | h5959
                      · linarith only [h5839, h5959, hlam]
                      · linarith only [h5955, h5959, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h5841, h5955, h5958, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5963 | h5963
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5964 | h5964
                      · linarith only [h5839, h5964, hlam]
                      · linarith only [h5955, h5957, h5963, h5964, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h5841, h5955, h5963, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5968 | h5968
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5969 | h5969
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5970 | h5970
                      · linarith only [h5839, h5970, hlam]
                      · linarith only [h5955, h5968, h5970, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h5956, h5968, h5969, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5974 | h5974
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5975 | h5975
                      · linarith only [h5839, h5975, hlam]
                      · linarith only [h5955, h5968, h5975, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h5956, h5974, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5979 | h5979
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5980 | h5980
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5981 | h5981
                      · linarith only [h5839, h5981, hlam]
                      · linarith only [h5955, h5981, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h5841, h5955, h5979, h5980, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5985 | h5985
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5986 | h5986
                      · linarith only [h5839, h5986, hlam]
                      · linarith only [h5955, h5979, h5986, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h5841, h5955, h5985, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h5953, h5956, hc26, hlam, p0_1]
                · linarith only [h5956, hc26, hlam, p0_1]
                · linarith only [h5955, h5956, hc26, hlam, p0_1]
              · rcases h6emax with h5993 | h5993 | h5993 | h5993 | h5993 | h5993
                · rcases m.htr 0 1 2 (by decide) (by decide) with h5994 | h5994
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h5995 | h5995
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h5996 | h5996
                      · linarith only [h5839, h5996, hlam]
                      · linarith only [h5996, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5841, h5994, h5995, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6000 | h6000
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6001 | h6001
                      · linarith only [h5839, h6001, hlam]
                      · linarith only [h5994, h6000, h6001, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h5841, h6000, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6005 | h6005
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6006 | h6006
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6007 | h6007
                      · linarith only [h5839, h6007, hlam]
                      · linarith only [h6005, h6007, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5993, h6005, h6006, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6011 | h6011
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6012 | h6012
                      · linarith only [h5839, h6012, hlam]
                      · linarith only [h6005, h6012, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h5993, h6011, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6016 | h6016
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6017 | h6017
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6018 | h6018
                      · linarith only [h5839, h6018, hlam]
                      · linarith only [h6018, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5841, h6017, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6022 | h6022
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6023 | h6023
                      · linarith only [h5839, h6023, hlam]
                      · linarith only [h6016, h6022, h6023, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h5841, h6022, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h5841, h5953, h5993, hc16, hlam, p0_1]
                · linarith only [h5841, h5993, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6029 | h6029
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6030 | h6030
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6031 | h6031
                      · linarith only [h5839, h6031, hlam]
                      · linarith only [h6031, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5841, h6029, h6030, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6035 | h6035
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6036 | h6036
                      · linarith only [h5839, h6036, hlam]
                      · linarith only [h6029, h6035, h6036, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h5841, h6035, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h5954, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6041 | h6041
            · rcases p0_3 (m.d 5 6) (by simp) with h6042 | h6042
              · rcases h6emax with h6043 | h6043 | h6043 | h6043 | h6043 | h6043
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6044 | h6044
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6045 | h6045
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6046 | h6046
                      · linarith only [h5839, h6046, hlam]
                      · linarith only [h6042, h6044, h6046, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h5841, h6042, h6044, h6045, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6050 | h6050
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6051 | h6051
                      · linarith only [h5839, h6051, hlam]
                      · linarith only [h6042, h6044, h6050, h6051, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h5841, h6042, h6050, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6055 | h6055
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6056 | h6056
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6057 | h6057
                      · linarith only [h5839, h6057, hlam]
                      · linarith only [h6042, h6055, h6057, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6043, h6055, h6056, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6061 | h6061
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6062 | h6062
                      · linarith only [h5839, h6062, hlam]
                      · linarith only [h6042, h6055, h6062, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h6043, h6061, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6066 | h6066
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6067 | h6067
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6068 | h6068
                      · linarith only [h5839, h6068, hlam]
                      · linarith only [h6042, h6068, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h5841, h6042, h6066, h6067, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6072 | h6072
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6073 | h6073
                      · linarith only [h5839, h6073, hlam]
                      · linarith only [h6042, h6066, h6072, h6073, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h5841, h6042, h6072, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6077 | h6077
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6078 | h6078
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6079 | h6079
                      · linarith only [h5839, h6079, hlam]
                      · linarith only [h6042, h6077, h6079, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h5841, h6042, h6077, h6078, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6083 | h6083
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6084 | h6084
                      · linarith only [h5839, h6084, hlam]
                      · linarith only [h6042, h6077, h6083, h6084, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h5841, h6042, h6083, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h5841, h6043, hc16, hlam, p0_1]
                · linarith only [h5841, h6042, h6043, hc16, hlam, p0_1]
              · rcases h6emax with h6090 | h6090 | h6090 | h6090 | h6090 | h6090
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6091 | h6091
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6092 | h6092
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6093 | h6093
                      · linarith only [h5839, h6093, hlam]
                      · linarith only [h6091, h6093, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5841, h6091, h6092, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6097 | h6097
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6098 | h6098
                      · linarith only [h5839, h6098, hlam]
                      · linarith only [h6091, h6098, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h5841, h6097, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6102 | h6102
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6103 | h6103
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6104 | h6104
                      · linarith only [h5839, h6104, hlam]
                      · linarith only [h6104, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6090, h6102, h6103, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6108 | h6108
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6109 | h6109
                      · linarith only [h5839, h6109, hlam]
                      · linarith only [h6102, h6108, h6109, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h6090, h6108, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6113 | h6113
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6114 | h6114
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6115 | h6115
                      · linarith only [h5839, h6115, hlam]
                      · linarith only [h6113, h6115, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5841, h6114, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6119 | h6119
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6120 | h6120
                      · linarith only [h5839, h6120, hlam]
                      · linarith only [h6113, h6119, h6120, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h5841, h6119, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6124 | h6124
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6125 | h6125
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6126 | h6126
                      · linarith only [h5839, h6126, hlam]
                      · linarith only [h6124, h6126, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5841, h6124, h6125, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6130 | h6130
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6131 | h6131
                      · linarith only [h5839, h6131, hlam]
                      · linarith only [h6124, h6131, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h5841, h6130, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h5841, h6090, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6136 | h6136
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6137 | h6137
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6138 | h6138
                      · linarith only [h5839, h6138, hlam]
                      · linarith only [h6138, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h5841, h6136, h6137, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6142 | h6142
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6143 | h6143
                      · linarith only [h5839, h6143, hlam]
                      · linarith only [h6136, h6142, h6143, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h5841, h6142, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h6041, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h6148 | h6148
    · linarith only [h6148, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h6150 | h6150
      · rcases p0_3 (m.d 2 6) (by simp) with h6151 | h6151
        · rcases p0_3 (m.d 3 6) (by simp) with h6152 | h6152
          · linarith only [h6152, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6154 | h6154
            · rcases p0_3 (m.d 5 6) (by simp) with h6155 | h6155
              · rcases h6emax with h6156 | h6156 | h6156 | h6156 | h6156 | h6156
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6157 | h6157
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6158 | h6158
                    · linarith only [h6150, h6158, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6158, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6161 | h6161
                    · linarith only [h6148, h6150, h6157, h6161, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6161, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6150, h6156, hc06, hlam, p0_1]
                · linarith only [h6148, h6151, h6156, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6166 | h6166
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6167 | h6167
                    · linarith only [h6148, h6150, h6167, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6166, h6167, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6170 | h6170
                    · linarith only [h6148, h6150, h6170, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6170, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6156, hc06, hlam, p0_1]
                · linarith only [h6148, h6155, h6156, hc06, hlam, p0_1]
              · rcases h6emax with h6175 | h6175 | h6175 | h6175 | h6175 | h6175
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6176 | h6176
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6177 | h6177
                    · linarith only [h6148, h6150, h6177, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6177, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6180 | h6180
                    · linarith only [h6148, h6150, h6176, h6180, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6180, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6150, h6175, hc06, hlam, p0_1]
                · linarith only [h6148, h6151, h6175, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6185 | h6185
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6186 | h6186
                    · linarith only [h6148, h6150, h6186, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6185, h6186, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6189 | h6189
                    · linarith only [h6148, h6150, h6185, h6189, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6189, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6175, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6193 | h6193
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6194 | h6194
                    · linarith only [h6148, h6150, h6194, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6193, h6194, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6197 | h6197
                    · linarith only [h6148, h6150, h6193, h6197, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6197, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h6154, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h6201 | h6201
          · linarith only [h6201, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6203 | h6203
            · rcases p0_3 (m.d 5 6) (by simp) with h6204 | h6204
              · rcases h6emax with h6205 | h6205 | h6205 | h6205 | h6205 | h6205
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6206 | h6206
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6207 | h6207
                    · linarith only [h6148, h6150, h6207, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6205, h6206, h6207, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6210 | h6210
                    · linarith only [h6148, h6150, h6210, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6210, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6150, h6205, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6214 | h6214
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6215 | h6215
                    · linarith only [h6148, h6150, h6215, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6215, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6218 | h6218
                    · linarith only [h6148, h6150, h6214, h6218, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6218, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6221 | h6221
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6222 | h6222
                    · linarith only [h6148, h6150, h6222, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6222, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6225 | h6225
                    · linarith only [h6148, h6150, h6221, h6225, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6225, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6205, hc06, hlam, p0_1]
                · linarith only [h6148, h6204, h6205, hc06, hlam, p0_1]
              · rcases h6emax with h6230 | h6230 | h6230 | h6230 | h6230 | h6230
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6231 | h6231
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6232 | h6232
                    · linarith only [h6148, h6150, h6232, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6232, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6235 | h6235
                    · linarith only [h6148, h6150, h6231, h6235, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6235, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6150, h6230, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6239 | h6239
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6240 | h6240
                    · linarith only [h6148, h6150, h6240, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6239, h6240, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6243 | h6243
                    · linarith only [h6148, h6150, h6239, h6243, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6243, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6246 | h6246
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6247 | h6247
                    · linarith only [h6148, h6150, h6247, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6247, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6250 | h6250
                    · linarith only [h6148, h6150, h6246, h6250, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6148, h6150, h6250, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6148, h6230, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6254 | h6254
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6255 | h6255
                    · linarith only [h6148, h6150, h6255, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6255, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6258 | h6258
                    · linarith only [h6148, h6150, h6258, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6148, h6150, h6258, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h6203, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h6262 | h6262
        · rcases p0_3 (m.d 3 6) (by simp) with h6263 | h6263
          · linarith only [h6263, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6265 | h6265
            · rcases p0_3 (m.d 5 6) (by simp) with h6266 | h6266
              · rcases h6emax with h6267 | h6267 | h6267 | h6267 | h6267 | h6267
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6268 | h6268
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6269 | h6269
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6270 | h6270
                      · linarith only [h6148, h6262, h6268, h6269, h6270, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h6148, h6266, h6270, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6150, h6266, h6268, h6269, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6274 | h6274
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6275 | h6275
                      · linarith only [h6148, h6262, h6274, h6275, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6266, h6275, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6150, h6266, h6274, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6279 | h6279
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6280 | h6280
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6281 | h6281
                      · linarith only [h6148, h6262, h6280, h6281, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6266, h6281, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6267, h6280, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6285 | h6285
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6286 | h6286
                      · linarith only [h6148, h6262, h6285, h6286, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6266, h6286, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6267, h6285, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h6148, h6262, h6267, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6291 | h6291
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6292 | h6292
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6293 | h6293
                      · linarith only [h6148, h6262, h6292, h6293, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6266, h6293, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6150, h6266, h6291, h6292, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6297 | h6297
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6298 | h6298
                      · linarith only [h6148, h6262, h6297, h6298, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6266, h6298, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6150, h6266, h6297, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h6148, h6267, hc06, hlam, p0_1]
                · linarith only [h6148, h6266, h6267, hc06, hlam, p0_1]
              · rcases h6emax with h6304 | h6304 | h6304 | h6304 | h6304 | h6304
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6305 | h6305
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6306 | h6306
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6307 | h6307
                      · linarith only [h6148, h6262, h6306, h6307, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6307, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6150, h6306, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6311 | h6311
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6312 | h6312
                      · linarith only [h6148, h6262, h6312, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6312, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6150, h6311, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6316 | h6316
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6317 | h6317
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6318 | h6318
                      · linarith only [h6148, h6262, h6318, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6318, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6304, h6316, h6317, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6322 | h6322
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6323 | h6323
                      · linarith only [h6148, h6262, h6323, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6323, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6304, h6322, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h6148, h6262, h6304, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6328 | h6328
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6329 | h6329
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6330 | h6330
                      · linarith only [h6148, h6262, h6329, h6330, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6330, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6150, h6329, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6334 | h6334
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6335 | h6335
                      · linarith only [h6148, h6262, h6335, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6335, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6150, h6334, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h6148, h6304, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6340 | h6340
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6341 | h6341
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6342 | h6342
                      · linarith only [h6148, h6262, h6341, h6342, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6342, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6150, h6341, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6346 | h6346
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6347 | h6347
                      · linarith only [h6148, h6262, h6347, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6148, h6262, h6347, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6150, h6346, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h6265, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h6352 | h6352
          · linarith only [h6352, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6354 | h6354
            · rcases p0_3 (m.d 5 6) (by simp) with h6355 | h6355
              · rcases h6emax with h6356 | h6356 | h6356 | h6356 | h6356 | h6356
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6357 | h6357
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6358 | h6358
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6359 | h6359
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6360 | h6360
                        · linarith only [h6148, h6360, hlam]
                        · linarith only [h6355, h6360, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6262, h6355, h6359, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6150, h6355, h6357, h6358, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6365 | h6365
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6366 | h6366
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6367 | h6367
                        · linarith only [h6148, h6367, hlam]
                        · linarith only [h6355, h6367, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6262, h6355, h6357, h6365, h6366, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h6150, h6355, h6365, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6372 | h6372
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6373 | h6373
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6374 | h6374
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6375 | h6375
                        · linarith only [h6148, h6375, hlam]
                        · linarith only [h6355, h6375, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6262, h6355, h6374, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6356, h6372, h6373, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6380 | h6380
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6381 | h6381
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6382 | h6382
                        · linarith only [h6148, h6382, hlam]
                        · linarith only [h6355, h6382, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6262, h6355, h6372, h6380, h6381, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h6356, h6380, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6387 | h6387
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6388 | h6388
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6389 | h6389
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6390 | h6390
                        · linarith only [h6148, h6390, hlam]
                        · linarith only [h6355, h6390, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6356, h6389, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h6150, h6355, h6388, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6395 | h6395
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6396 | h6396
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6397 | h6397
                        · linarith only [h6148, h6397, hlam]
                        · linarith only [h6355, h6397, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6356, h6387, h6395, h6396, hc16, hlam]
                    · linarith only [h6150, h6355, h6395, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6402 | h6402
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6403 | h6403
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6404 | h6404
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6405 | h6405
                        · linarith only [h6148, h6405, hlam]
                        · linarith only [h6355, h6405, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6262, h6355, h6404, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6150, h6355, h6402, h6403, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6410 | h6410
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6411 | h6411
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6412 | h6412
                        · linarith only [h6148, h6412, hlam]
                        · linarith only [h6355, h6412, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h6262, h6355, h6402, h6410, h6411, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h6150, h6355, h6410, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h6150, h6356, hc16, hlam, p0_1]
                · linarith only [h6150, h6355, h6356, hc16, hlam, p0_1]
              · rcases h6emax with h6419 | h6419 | h6419 | h6419 | h6419 | h6419
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6420 | h6420
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6421 | h6421
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6422 | h6422
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6423 | h6423
                        · linarith only [h6148, h6423, hlam]
                        · linarith only [h6423, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6422, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6150, h6420, h6421, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6428 | h6428
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6429 | h6429
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6430 | h6430
                        · linarith only [h6148, h6430, hlam]
                        · linarith only [h6430, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6420, h6429, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6150, h6428, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6435 | h6435
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6436 | h6436
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6437 | h6437
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6438 | h6438
                        · linarith only [h6148, h6438, hlam]
                        · linarith only [h6438, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6437, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6419, h6435, h6436, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6443 | h6443
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6444 | h6444
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6445 | h6445
                        · linarith only [h6148, h6445, hlam]
                        · linarith only [h6445, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6435, h6444, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6419, h6443, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6450 | h6450
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6451 | h6451
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6452 | h6452
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6453 | h6453
                        · linarith only [h6148, h6453, hlam]
                        · linarith only [h6453, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6419, h6452, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h6150, h6451, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6458 | h6458
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6459 | h6459
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6460 | h6460
                        · linarith only [h6148, h6460, hlam]
                        · linarith only [h6460, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6419, h6450, h6458, h6459, hc16, hlam]
                    · linarith only [h6150, h6458, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6465 | h6465
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6466 | h6466
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6467 | h6467
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6468 | h6468
                        · linarith only [h6148, h6468, hlam]
                        · linarith only [h6468, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6467, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6150, h6465, h6466, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6473 | h6473
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6474 | h6474
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6475 | h6475
                        · linarith only [h6148, h6475, hlam]
                        · linarith only [h6475, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6465, h6474, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6150, h6473, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h6150, h6419, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6481 | h6481
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6482 | h6482
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6483 | h6483
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6484 | h6484
                        · linarith only [h6148, h6484, hlam]
                        · linarith only [h6484, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6483, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6150, h6481, h6482, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6489 | h6489
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6490 | h6490
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6491 | h6491
                        · linarith only [h6148, h6491, hlam]
                        · linarith only [h6491, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6262, h6481, h6490, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6150, h6489, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h6354, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h6498 | h6498
    · linarith only [h6498, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h6500 | h6500
      · rcases p0_3 (m.d 2 6) (by simp) with h6501 | h6501
        · rcases p0_3 (m.d 3 6) (by simp) with h6502 | h6502
          · rcases p0_3 (m.d 4 6) (by simp) with h6503 | h6503
            · rcases p0_3 (m.d 5 6) (by simp) with h6504 | h6504
              · linarith only [h6504, hlam, p0_0]
              · rcases h6emax with h6506 | h6506 | h6506 | h6506 | h6506 | h6506
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6507 | h6507
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6508 | h6508
                    · linarith only [h6500, h6508, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6506, h6507, h6508, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6511 | h6511
                    · linarith only [h6498, h6500, h6511, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6511, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6498, h6500, h6506, hc06, hlam, p0_1]
                · linarith only [h6498, h6501, h6506, hc06, hlam, p0_1]
                · linarith only [h6498, h6502, h6506, hc06, hlam, p0_1]
                · linarith only [h6498, h6506, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6518 | h6518
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6519 | h6519
                    · linarith only [h6498, h6500, h6519, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6519, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6522 | h6522
                    · linarith only [h6498, h6500, h6518, h6522, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6522, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h6503, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6526 | h6526
            · rcases p0_3 (m.d 5 6) (by simp) with h6527 | h6527
              · linarith only [h6527, hlam, p0_0]
              · rcases h6emax with h6529 | h6529 | h6529 | h6529 | h6529 | h6529
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6530 | h6530
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6531 | h6531
                    · linarith only [h6498, h6500, h6531, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6529, h6530, h6531, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6534 | h6534
                    · linarith only [h6498, h6500, h6530, h6534, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6534, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6498, h6500, h6529, hc06, hlam, p0_1]
                · linarith only [h6498, h6501, h6529, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6539 | h6539
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6540 | h6540
                    · linarith only [h6498, h6500, h6540, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6539, h6540, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6543 | h6543
                    · linarith only [h6498, h6500, h6543, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6543, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6498, h6529, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6547 | h6547
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6548 | h6548
                    · linarith only [h6498, h6500, h6548, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6547, h6548, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6551 | h6551
                    · linarith only [h6498, h6500, h6547, h6551, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6551, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h6526, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h6555 | h6555
          · rcases p0_3 (m.d 4 6) (by simp) with h6556 | h6556
            · rcases p0_3 (m.d 5 6) (by simp) with h6557 | h6557
              · linarith only [h6557, hlam, p0_0]
              · rcases h6emax with h6559 | h6559 | h6559 | h6559 | h6559 | h6559
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6560 | h6560
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6561 | h6561
                    · linarith only [h6498, h6500, h6561, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6559, h6560, h6561, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6564 | h6564
                    · linarith only [h6498, h6500, h6560, h6564, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6564, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6498, h6500, h6559, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6568 | h6568
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6569 | h6569
                    · linarith only [h6498, h6500, h6569, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6569, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6572 | h6572
                    · linarith only [h6498, h6500, h6568, h6572, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6572, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6498, h6555, h6559, hc06, hlam, p0_1]
                · linarith only [h6498, h6559, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6577 | h6577
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6578 | h6578
                    · linarith only [h6498, h6500, h6578, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6578, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6581 | h6581
                    · linarith only [h6498, h6500, h6577, h6581, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6581, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h6556, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6585 | h6585
            · rcases p0_3 (m.d 5 6) (by simp) with h6586 | h6586
              · linarith only [h6586, hlam, p0_0]
              · rcases h6emax with h6588 | h6588 | h6588 | h6588 | h6588 | h6588
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6589 | h6589
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6590 | h6590
                    · linarith only [h6498, h6500, h6590, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6590, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6593 | h6593
                    · linarith only [h6498, h6500, h6589, h6593, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6593, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6498, h6500, h6588, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6597 | h6597
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6598 | h6598
                    · linarith only [h6498, h6500, h6598, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6598, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6601 | h6601
                    · linarith only [h6498, h6500, h6597, h6601, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6601, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6604 | h6604
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6605 | h6605
                    · linarith only [h6498, h6500, h6605, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6604, h6605, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6608 | h6608
                    · linarith only [h6498, h6500, h6604, h6608, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6608, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6498, h6588, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6612 | h6612
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6613 | h6613
                    · linarith only [h6498, h6500, h6613, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6498, h6500, h6612, h6613, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6616 | h6616
                    · linarith only [h6498, h6500, h6612, h6616, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6498, h6500, h6616, hc01, hc16, hlam, hphi, p0_1]
            · linarith only [h6585, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h6620 | h6620
        · rcases p0_3 (m.d 3 6) (by simp) with h6621 | h6621
          · rcases p0_3 (m.d 4 6) (by simp) with h6622 | h6622
            · rcases p0_3 (m.d 5 6) (by simp) with h6623 | h6623
              · linarith only [h6623, hlam, p0_0]
              · rcases h6emax with h6625 | h6625 | h6625 | h6625 | h6625 | h6625
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6626 | h6626
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6627 | h6627
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6628 | h6628
                      · linarith only [h6498, h6620, h6626, h6628, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h6498, h6620, h6628, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6627, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6632 | h6632
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6633 | h6633
                      · linarith only [h6498, h6620, h6633, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6633, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6632, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6637 | h6637
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6638 | h6638
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6639 | h6639
                      · linarith only [h6498, h6620, h6639, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6639, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6625, h6638, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6643 | h6643
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6644 | h6644
                      · linarith only [h6498, h6620, h6644, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6644, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6625, h6643, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h6498, h6620, h6625, hc06, hlam, p0_1]
                · linarith only [h6498, h6621, h6625, hc06, hlam, p0_1]
                · linarith only [h6498, h6625, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6651 | h6651
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6652 | h6652
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6653 | h6653
                      · linarith only [h6498, h6620, h6652, h6653, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6653, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6652, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6657 | h6657
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6658 | h6658
                      · linarith only [h6498, h6620, h6658, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6658, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6657, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h6622, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6663 | h6663
            · rcases p0_3 (m.d 5 6) (by simp) with h6664 | h6664
              · linarith only [h6664, hlam, p0_0]
              · rcases h6emax with h6666 | h6666 | h6666 | h6666 | h6666 | h6666
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6667 | h6667
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6668 | h6668
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6669 | h6669
                      · linarith only [h6498, h6620, h6669, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6669, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6668, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6673 | h6673
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6674 | h6674
                      · linarith only [h6498, h6620, h6674, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6674, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6673, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6678 | h6678
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6679 | h6679
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6680 | h6680
                      · linarith only [h6498, h6620, h6680, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6680, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6666, h6679, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6684 | h6684
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6685 | h6685
                      · linarith only [h6498, h6620, h6685, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6685, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6666, h6684, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h6498, h6620, h6666, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6690 | h6690
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6691 | h6691
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6692 | h6692
                      · linarith only [h6498, h6620, h6691, h6692, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6692, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6691, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6696 | h6696
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6697 | h6697
                      · linarith only [h6498, h6620, h6697, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6697, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6696, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h6498, h6666, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6702 | h6702
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6703 | h6703
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6704 | h6704
                      · linarith only [h6498, h6620, h6703, h6704, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6704, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6703, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6708 | h6708
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6709 | h6709
                      · linarith only [h6498, h6620, h6709, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h6498, h6620, h6709, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h6500, h6708, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h6663, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h6714 | h6714
          · rcases p0_3 (m.d 4 6) (by simp) with h6715 | h6715
            · rcases p0_3 (m.d 5 6) (by simp) with h6716 | h6716
              · linarith only [h6716, hlam, p0_0]
              · rcases h6emax with h6718 | h6718 | h6718 | h6718 | h6718 | h6718
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6719 | h6719
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6720 | h6720
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6721 | h6721
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6722 | h6722
                        · linarith only [h6498, h6714, h6722, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6722, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6620, h6721, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6500, h6720, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6727 | h6727
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6728 | h6728
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6729 | h6729
                        · linarith only [h6498, h6714, h6729, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6729, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6620, h6719, h6727, h6728, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h6500, h6727, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6734 | h6734
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6735 | h6735
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6736 | h6736
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6737 | h6737
                        · linarith only [h6498, h6714, h6737, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6737, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6620, h6736, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6718, h6734, h6735, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6742 | h6742
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6743 | h6743
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6744 | h6744
                        · linarith only [h6498, h6714, h6744, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6744, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6620, h6734, h6743, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6718, h6742, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6749 | h6749
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6750 | h6750
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6751 | h6751
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6752 | h6752
                        · linarith only [h6498, h6714, h6752, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6752, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6718, h6751, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h6500, h6749, h6750, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6757 | h6757
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6758 | h6758
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6759 | h6759
                        · linarith only [h6498, h6714, h6759, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6759, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6718, h6749, h6757, h6758, hc16, hlam]
                    · linarith only [h6500, h6757, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h6498, h6714, h6718, hc06, hlam, p0_1]
                · linarith only [h6498, h6718, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6766 | h6766
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6767 | h6767
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6768 | h6768
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6769 | h6769
                        · linarith only [h6498, h6714, h6767, h6769, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6769, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6620, h6768, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6500, h6766, h6767, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6774 | h6774
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6775 | h6775
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6776 | h6776
                        · linarith only [h6498, h6714, h6776, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h6498, h6714, h6776, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h6620, h6766, h6775, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6500, h6774, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h6715, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6782 | h6782
            · rcases p0_3 (m.d 5 6) (by simp) with h6783 | h6783
              · linarith only [h6783, hlam, p0_0]
              · rcases h6emax with h6785 | h6785 | h6785 | h6785 | h6785 | h6785
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6786 | h6786
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6787 | h6787
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6788 | h6788
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6789 | h6789
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6790 | h6790
                          · linarith only [h6498, h6790, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6790, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6789, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6620, h6788, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6500, h6786, h6787, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6796 | h6796
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6797 | h6797
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6798 | h6798
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6799 | h6799
                          · linarith only [h6498, h6799, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6799, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6798, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6620, h6786, h6796, h6797, hc16, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1]
                    · linarith only [h6500, h6796, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6805 | h6805
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6806 | h6806
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6807 | h6807
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6808 | h6808
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6809 | h6809
                          · linarith only [h6498, h6809, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6809, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6808, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6620, h6807, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6785, h6805, h6806, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6815 | h6815
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6816 | h6816
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6817 | h6817
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6818 | h6818
                          · linarith only [h6498, h6818, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6818, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6817, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6620, h6816, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6785, h6815, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6824 | h6824
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6825 | h6825
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6826 | h6826
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6827 | h6827
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6828 | h6828
                          · linarith only [h6498, h6828, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6828, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6827, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6785, h6826, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h6500, h6825, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6834 | h6834
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6835 | h6835
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6836 | h6836
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6837 | h6837
                          · linarith only [h6498, h6837, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6837, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6836, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6785, h6824, h6834, h6835, hc16, hlam]
                    · linarith only [h6500, h6834, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6843 | h6843
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6844 | h6844
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6845 | h6845
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6846 | h6846
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6847 | h6847
                          · linarith only [h6498, h6847, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6847, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6785, h6846, hc03, hlam, ht34, ht45, ht56]
                      · linarith only [h6620, h6845, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6500, h6843, h6844, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6853 | h6853
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6854 | h6854
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6855 | h6855
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6856 | h6856
                          · linarith only [h6498, h6856, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6856, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6785, h6855, hc03, hlam, ht34, ht45, ht56]
                      · linarith only [h6620, h6843, h6854, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6500, h6853, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                · linarith only [h6498, h6785, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6863 | h6863
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6864 | h6864
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6865 | h6865
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6866 | h6866
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6867 | h6867
                          · linarith only [h6498, h6864, h6867, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6867, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6866, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6620, h6865, hc02, hc46, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h6500, h6863, h6864, hc12, hc46, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6873 | h6873
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h6874 | h6874
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h6875 | h6875
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h6876 | h6876
                          · linarith only [h6498, h6876, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h6498, h6876, hc04, hc46, hlam, hphi, p0_1]
                        · linarith only [h6714, h6875, hc03, hc46, hlam, hphi, ht34, p0_1]
                      · linarith only [h6620, h6863, h6874, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h6500, h6873, hc01, hc46, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h6782, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h6883 | h6883
    · linarith only [h6883, hlam, p0_0]
    · rcases p0_3 (m.d 1 6) (by simp) with h6885 | h6885
      · rcases p0_3 (m.d 2 6) (by simp) with h6886 | h6886
        · rcases p0_3 (m.d 3 6) (by simp) with h6887 | h6887
          · rcases p0_3 (m.d 4 6) (by simp) with h6888 | h6888
            · rcases p0_3 (m.d 5 6) (by simp) with h6889 | h6889
              · rcases h6emax with h6890 | h6890 | h6890 | h6890 | h6890 | h6890
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6891 | h6891
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6892 | h6892
                    · linarith only [h6885, h6892, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6890, h6891, h6892, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6895 | h6895
                    · linarith only [h6885, h6891, h6895, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h6895, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h6890, hc06, hlam, p0_1]
                · linarith only [h6886, h6890, hc06, hlam, p0_1]
                · linarith only [h6887, h6890, hc06, hlam, p0_1]
                · linarith only [h6888, h6890, hc06, hlam, p0_1]
                · linarith only [h6890, hc06, hlam, p0_1]
              · linarith only [h6889, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h6904 | h6904
              · rcases h6emax with h6905 | h6905 | h6905 | h6905 | h6905 | h6905
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6906 | h6906
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6907 | h6907
                    · linarith only [h6885, h6907, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6905, h6906, h6907, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6910 | h6910
                    · linarith only [h6885, h6910, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6910, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h6905, hc06, hlam, p0_1]
                · linarith only [h6886, h6905, hc06, hlam, p0_1]
                · linarith only [h6887, h6905, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6916 | h6916
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6917 | h6917
                    · linarith only [h6885, h6917, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6916, h6917, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6920 | h6920
                    · linarith only [h6885, h6920, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6920, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6905, hc06, hlam, p0_1]
              · linarith only [h6904, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h6925 | h6925
            · rcases p0_3 (m.d 5 6) (by simp) with h6926 | h6926
              · rcases h6emax with h6927 | h6927 | h6927 | h6927 | h6927 | h6927
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6928 | h6928
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6929 | h6929
                    · linarith only [h6885, h6929, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6927, h6928, h6929, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6932 | h6932
                    · linarith only [h6885, h6932, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6932, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h6927, hc06, hlam, p0_1]
                · linarith only [h6886, h6927, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6937 | h6937
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6938 | h6938
                    · linarith only [h6885, h6938, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6938, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6941 | h6941
                    · linarith only [h6885, h6937, h6941, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h6941, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6925, h6927, hc06, hlam, p0_1]
                · linarith only [h6927, hc06, hlam, p0_1]
              · linarith only [h6926, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h6947 | h6947
              · rcases h6emax with h6948 | h6948 | h6948 | h6948 | h6948 | h6948
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6949 | h6949
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6950 | h6950
                    · linarith only [h6885, h6950, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6948, h6949, h6950, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6953 | h6953
                    · linarith only [h6885, h6953, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6953, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h6948, hc06, hlam, p0_1]
                · linarith only [h6886, h6948, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6958 | h6958
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6959 | h6959
                    · linarith only [h6885, h6959, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6958, h6959, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6962 | h6962
                    · linarith only [h6885, h6958, h6962, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h6962, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6965 | h6965
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6966 | h6966
                    · linarith only [h6885, h6966, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6966, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6969 | h6969
                    · linarith only [h6885, h6969, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6969, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6948, hc06, hlam, p0_1]
              · linarith only [h6947, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h6974 | h6974
          · rcases p0_3 (m.d 4 6) (by simp) with h6975 | h6975
            · rcases p0_3 (m.d 5 6) (by simp) with h6976 | h6976
              · rcases h6emax with h6977 | h6977 | h6977 | h6977 | h6977 | h6977
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6978 | h6978
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6979 | h6979
                    · linarith only [h6885, h6979, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6979, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6982 | h6982
                    · linarith only [h6885, h6982, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6982, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h6977, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6986 | h6986
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6987 | h6987
                    · linarith only [h6885, h6987, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6986, h6987, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h6990 | h6990
                    · linarith only [h6885, h6990, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h6990, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6974, h6977, hc06, hlam, p0_1]
                · linarith only [h6975, h6977, hc06, hlam, p0_1]
                · linarith only [h6977, hc06, hlam, p0_1]
              · linarith only [h6976, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h6997 | h6997
              · rcases h6emax with h6998 | h6998 | h6998 | h6998 | h6998 | h6998
                · rcases m.htr 0 1 2 (by decide) (by decide) with h6999 | h6999
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7000 | h7000
                    · linarith only [h6885, h7000, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7000, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7003 | h7003
                    · linarith only [h6885, h6999, h7003, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h7003, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h6998, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7007 | h7007
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7008 | h7008
                    · linarith only [h6885, h7008, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7008, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7011 | h7011
                    · linarith only [h6885, h7007, h7011, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h7011, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6974, h6998, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7015 | h7015
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7016 | h7016
                    · linarith only [h6885, h7016, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7015, h7016, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7019 | h7019
                    · linarith only [h6885, h7019, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7019, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6998, hc06, hlam, p0_1]
              · linarith only [h6997, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h7024 | h7024
            · rcases p0_3 (m.d 5 6) (by simp) with h7025 | h7025
              · rcases h6emax with h7026 | h7026 | h7026 | h7026 | h7026 | h7026
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7027 | h7027
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7028 | h7028
                    · linarith only [h6885, h7028, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7026, h7027, h7028, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7031 | h7031
                    · linarith only [h6885, h7031, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7031, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h7026, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7035 | h7035
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7036 | h7036
                    · linarith only [h6885, h7036, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7035, h7036, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7039 | h7039
                    · linarith only [h6885, h7039, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7039, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7042 | h7042
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7043 | h7043
                    · linarith only [h6885, h7043, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7042, h7043, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7046 | h7046
                    · linarith only [h6885, h7042, h7046, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h7046, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7024, h7026, hc06, hlam, p0_1]
                · linarith only [h7026, hc06, hlam, p0_1]
              · linarith only [h7025, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7052 | h7052
              · rcases h6emax with h7053 | h7053 | h7053 | h7053 | h7053 | h7053
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7054 | h7054
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7055 | h7055
                    · linarith only [h6885, h7055, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7055, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7058 | h7058
                    · linarith only [h6885, h7054, h7058, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h7058, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h6885, h7053, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7062 | h7062
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7063 | h7063
                    · linarith only [h6885, h7063, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7063, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7066 | h7066
                    · linarith only [h6885, h7062, h7066, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h7066, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7069 | h7069
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7070 | h7070
                    · linarith only [h6885, h7070, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7069, h7070, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7073 | h7073
                    · linarith only [h6885, h7069, h7073, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h6885, h7073, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7076 | h7076
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7077 | h7077
                    · linarith only [h6885, h7077, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7076, h7077, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7080 | h7080
                    · linarith only [h6885, h7080, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h6885, h7080, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7053, hc06, hlam, p0_1]
              · linarith only [h7052, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h7085 | h7085
        · rcases p0_3 (m.d 3 6) (by simp) with h7086 | h7086
          · rcases p0_3 (m.d 4 6) (by simp) with h7087 | h7087
            · rcases p0_3 (m.d 5 6) (by simp) with h7088 | h7088
              · rcases h6emax with h7089 | h7089 | h7089 | h7089 | h7089 | h7089
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7090 | h7090
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7091 | h7091
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7092 | h7092
                      · linarith only [h7085, h7090, h7091, h7092, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h7092, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7091, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7096 | h7096
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7097 | h7097
                      · linarith only [h7085, h7096, h7097, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7090, h7097, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7096, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7101 | h7101
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7102 | h7102
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7103 | h7103
                      · linarith only [h7085, h7102, h7103, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7103, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7102, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7107 | h7107
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7108 | h7108
                      · linarith only [h7085, h7107, h7108, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7108, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7107, hlam]
                · linarith only [h7085, h7089, hc06, hlam, p0_1]
                · linarith only [h7086, h7089, hc06, hlam, p0_1]
                · linarith only [h7087, h7089, hc06, hlam, p0_1]
                · linarith only [h7089, hc06, hlam, p0_1]
              · linarith only [h7088, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7117 | h7117
              · rcases h6emax with h7118 | h7118 | h7118 | h7118 | h7118 | h7118
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7119 | h7119
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7120 | h7120
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7121 | h7121
                      · linarith only [h7085, h7120, h7121, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7121, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7120, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7125 | h7125
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7126 | h7126
                      · linarith only [h7085, h7125, h7126, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7126, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7125, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7130 | h7130
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7131 | h7131
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7132 | h7132
                      · linarith only [h7085, h7131, h7132, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7132, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7131, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7136 | h7136
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7137 | h7137
                      · linarith only [h7085, h7136, h7137, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7137, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7136, hlam]
                · linarith only [h7085, h7118, hc06, hlam, p0_1]
                · linarith only [h7086, h7118, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7143 | h7143
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7144 | h7144
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7145 | h7145
                      · linarith only [h7085, h7144, h7145, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7145, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7144, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7149 | h7149
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7150 | h7150
                      · linarith only [h7085, h7149, h7150, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7150, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7149, hlam]
                · linarith only [h7118, hc06, hlam, p0_1]
              · linarith only [h7117, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h7156 | h7156
            · rcases p0_3 (m.d 5 6) (by simp) with h7157 | h7157
              · rcases h6emax with h7158 | h7158 | h7158 | h7158 | h7158 | h7158
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7159 | h7159
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7160 | h7160
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7161 | h7161
                      · linarith only [h7085, h7160, h7161, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7161, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7160, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7165 | h7165
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7166 | h7166
                      · linarith only [h7085, h7165, h7166, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7166, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7165, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7170 | h7170
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7171 | h7171
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7172 | h7172
                      · linarith only [h7085, h7171, h7172, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7172, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7171, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7176 | h7176
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7177 | h7177
                      · linarith only [h7085, h7176, h7177, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7177, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7176, hlam]
                · linarith only [h7085, h7158, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7182 | h7182
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7183 | h7183
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7184 | h7184
                      · linarith only [h7085, h7183, h7184, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7184, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7183, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7188 | h7188
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7189 | h7189
                      · linarith only [h7085, h7188, h7189, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7189, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7188, hlam]
                · linarith only [h7156, h7158, hc06, hlam, p0_1]
                · linarith only [h7158, hc06, hlam, p0_1]
              · linarith only [h7157, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7196 | h7196
              · rcases h6emax with h7197 | h7197 | h7197 | h7197 | h7197 | h7197
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7198 | h7198
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7199 | h7199
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7200 | h7200
                      · linarith only [h7085, h7199, h7200, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7200, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7199, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7204 | h7204
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7205 | h7205
                      · linarith only [h7085, h7204, h7205, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7205, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7204, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7209 | h7209
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7210 | h7210
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7211 | h7211
                      · linarith only [h7085, h7210, h7211, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7211, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7210, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7215 | h7215
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7216 | h7216
                      · linarith only [h7085, h7215, h7216, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7216, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7215, hlam]
                · linarith only [h7085, h7197, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7221 | h7221
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7222 | h7222
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7223 | h7223
                      · linarith only [h7085, h7222, h7223, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7223, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7222, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7227 | h7227
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7228 | h7228
                      · linarith only [h7085, h7227, h7228, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7228, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7227, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7232 | h7232
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7233 | h7233
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7234 | h7234
                      · linarith only [h7085, h7233, h7234, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7234, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7233, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7238 | h7238
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7239 | h7239
                      · linarith only [h7085, h7238, h7239, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h7239, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h6885, h7238, hlam]
                · linarith only [h7197, hc06, hlam, p0_1]
              · linarith only [h7196, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h7245 | h7245
          · rcases p0_3 (m.d 4 6) (by simp) with h7246 | h7246
            · rcases p0_3 (m.d 5 6) (by simp) with h7247 | h7247
              · rcases h6emax with h7248 | h7248 | h7248 | h7248 | h7248 | h7248
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7249 | h7249
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7250 | h7250
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7251 | h7251
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7252 | h7252
                        · linarith only [h7245, h7250, h7252, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7252, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7251, hlam]
                    · linarith only [h6885, h7250, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7257 | h7257
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7258 | h7258
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7259 | h7259
                        · linarith only [h7245, h7257, h7259, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7259, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7258, hlam]
                    · linarith only [h6885, h7257, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7264 | h7264
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7265 | h7265
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7266 | h7266
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7267 | h7267
                        · linarith only [h7245, h7265, h7267, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7267, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7266, hlam]
                    · linarith only [h6885, h7265, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7272 | h7272
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7273 | h7273
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7274 | h7274
                        · linarith only [h7245, h7272, h7274, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7274, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7273, hlam]
                    · linarith only [h6885, h7272, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7279 | h7279
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7280 | h7280
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7281 | h7281
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7282 | h7282
                        · linarith only [h7245, h7280, h7282, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7282, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7281, hlam]
                    · linarith only [h6885, h7280, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7287 | h7287
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7288 | h7288
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7289 | h7289
                        · linarith only [h7245, h7287, h7289, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7289, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7288, hlam]
                    · linarith only [h6885, h7287, hlam]
                · linarith only [h7245, h7248, hc06, hlam, p0_1]
                · linarith only [h7246, h7248, hc06, hlam, p0_1]
                · linarith only [h7248, hc06, hlam, p0_1]
              · linarith only [h7247, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7298 | h7298
              · rcases h6emax with h7299 | h7299 | h7299 | h7299 | h7299 | h7299
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7300 | h7300
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7301 | h7301
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7302 | h7302
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7303 | h7303
                        · linarith only [h7245, h7301, h7303, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7303, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7302, hlam]
                    · linarith only [h6885, h7301, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7308 | h7308
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7309 | h7309
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7310 | h7310
                        · linarith only [h7245, h7308, h7310, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7310, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7309, hlam]
                    · linarith only [h6885, h7308, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7315 | h7315
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7316 | h7316
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7317 | h7317
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7318 | h7318
                        · linarith only [h7245, h7316, h7318, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7318, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7317, hlam]
                    · linarith only [h6885, h7316, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7323 | h7323
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7324 | h7324
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7325 | h7325
                        · linarith only [h7245, h7323, h7325, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7325, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7324, hlam]
                    · linarith only [h6885, h7323, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7330 | h7330
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7331 | h7331
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7332 | h7332
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7333 | h7333
                        · linarith only [h7245, h7331, h7333, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7333, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7332, hlam]
                    · linarith only [h6885, h7331, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7338 | h7338
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7339 | h7339
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7340 | h7340
                        · linarith only [h7245, h7338, h7340, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7340, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7339, hlam]
                    · linarith only [h6885, h7338, hlam]
                · linarith only [h7245, h7299, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7346 | h7346
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7347 | h7347
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7348 | h7348
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7349 | h7349
                        · linarith only [h7245, h7347, h7349, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7349, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7348, hlam]
                    · linarith only [h6885, h7347, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7354 | h7354
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7355 | h7355
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7356 | h7356
                        · linarith only [h7245, h7354, h7356, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h7356, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h7085, h7355, hlam]
                    · linarith only [h6885, h7354, hlam]
                · linarith only [h7299, hc06, hlam, p0_1]
              · linarith only [h7298, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h7363 | h7363
            · rcases p0_3 (m.d 5 6) (by simp) with h7364 | h7364
              · rcases h6emax with h7365 | h7365 | h7365 | h7365 | h7365 | h7365
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7366 | h7366
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7367 | h7367
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7368 | h7368
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7369 | h7369
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7370 | h7370
                          · linarith only [h7363, h7367, h7370, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7370, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7369, hlam]
                      · linarith only [h7085, h7368, hlam]
                    · linarith only [h6885, h7367, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7376 | h7376
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7377 | h7377
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7378 | h7378
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7379 | h7379
                          · linarith only [h7363, h7376, h7379, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7379, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7378, hlam]
                      · linarith only [h7085, h7377, hlam]
                    · linarith only [h6885, h7376, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7385 | h7385
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7386 | h7386
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7387 | h7387
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7388 | h7388
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7389 | h7389
                          · linarith only [h7363, h7386, h7389, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7389, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7388, hlam]
                      · linarith only [h7085, h7387, hlam]
                    · linarith only [h6885, h7386, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7395 | h7395
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7396 | h7396
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7397 | h7397
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7398 | h7398
                          · linarith only [h7363, h7395, h7398, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7398, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7397, hlam]
                      · linarith only [h7085, h7396, hlam]
                    · linarith only [h6885, h7395, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7404 | h7404
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7405 | h7405
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7406 | h7406
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7407 | h7407
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7408 | h7408
                          · linarith only [h7363, h7405, h7408, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7408, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7407, hlam]
                      · linarith only [h7085, h7406, hlam]
                    · linarith only [h6885, h7405, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7414 | h7414
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7415 | h7415
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7416 | h7416
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7417 | h7417
                          · linarith only [h7363, h7414, h7417, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7417, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7416, hlam]
                      · linarith only [h7085, h7415, hlam]
                    · linarith only [h6885, h7414, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7423 | h7423
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7424 | h7424
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7425 | h7425
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7426 | h7426
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7427 | h7427
                          · linarith only [h7363, h7424, h7427, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7427, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7426, hlam]
                      · linarith only [h7085, h7425, hlam]
                    · linarith only [h6885, h7424, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7433 | h7433
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7434 | h7434
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7435 | h7435
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7436 | h7436
                          · linarith only [h7363, h7433, h7436, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo3]
                          · linarith only [h7436, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h7245, h7435, hlam]
                      · linarith only [h7085, h7434, hlam]
                    · linarith only [h6885, h7433, hlam]
                · linarith only [h7363, h7365, hc06, hlam, p0_1]
                · linarith only [h7365, hc06, hlam, p0_1]
              · linarith only [h7364, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7445 | h7445
              · rcases h6emax with h7446 | h7446 | h7446 | h7446 | h7446 | h7446
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7447 | h7447
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7448 | h7448
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7449 | h7449
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7450 | h7450
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7451 | h7451
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7452 | h7452
                            · linarith only [h7452, hlam, p0_0]
                            · linarith only [h7452, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7451, hlam]
                        · linarith only [h7245, h7450, hlam]
                      · linarith only [h7085, h7449, hlam]
                    · linarith only [h6885, h7448, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7459 | h7459
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7460 | h7460
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7461 | h7461
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7462 | h7462
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7463 | h7463
                            · linarith only [h7463, hlam, p0_0]
                            · linarith only [h7463, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7462, hlam]
                        · linarith only [h7245, h7461, hlam]
                      · linarith only [h7085, h7460, hlam]
                    · linarith only [h6885, h7459, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7470 | h7470
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7471 | h7471
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7472 | h7472
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7473 | h7473
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7474 | h7474
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7475 | h7475
                            · linarith only [h7475, hlam, p0_0]
                            · linarith only [h7475, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7474, hlam]
                        · linarith only [h7245, h7473, hlam]
                      · linarith only [h7085, h7472, hlam]
                    · linarith only [h6885, h7471, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7482 | h7482
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7483 | h7483
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7484 | h7484
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7485 | h7485
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7486 | h7486
                            · linarith only [h7486, hlam, p0_0]
                            · linarith only [h7486, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7485, hlam]
                        · linarith only [h7245, h7484, hlam]
                      · linarith only [h7085, h7483, hlam]
                    · linarith only [h6885, h7482, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7493 | h7493
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7494 | h7494
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7495 | h7495
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7496 | h7496
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7497 | h7497
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7498 | h7498
                            · linarith only [h7498, hlam, p0_0]
                            · linarith only [h7498, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7497, hlam]
                        · linarith only [h7245, h7496, hlam]
                      · linarith only [h7085, h7495, hlam]
                    · linarith only [h6885, h7494, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7505 | h7505
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7506 | h7506
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7507 | h7507
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7508 | h7508
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7509 | h7509
                            · linarith only [h7509, hlam, p0_0]
                            · linarith only [h7509, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7508, hlam]
                        · linarith only [h7245, h7507, hlam]
                      · linarith only [h7085, h7506, hlam]
                    · linarith only [h6885, h7505, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7516 | h7516
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7517 | h7517
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7518 | h7518
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7519 | h7519
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7520 | h7520
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7521 | h7521
                            · linarith only [h7521, hlam, p0_0]
                            · linarith only [h7521, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7520, hlam]
                        · linarith only [h7245, h7519, hlam]
                      · linarith only [h7085, h7518, hlam]
                    · linarith only [h6885, h7517, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7528 | h7528
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7529 | h7529
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7530 | h7530
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7531 | h7531
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7532 | h7532
                            · linarith only [h7532, hlam, p0_0]
                            · linarith only [h7532, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7531, hlam]
                        · linarith only [h7245, h7530, hlam]
                      · linarith only [h7085, h7529, hlam]
                    · linarith only [h6885, h7528, hlam]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7539 | h7539
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7540 | h7540
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7541 | h7541
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7542 | h7542
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7543 | h7543
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7544 | h7544
                            · linarith only [h7544, hlam, p0_0]
                            · linarith only [h7544, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7543, hlam]
                        · linarith only [h7245, h7542, hlam]
                      · linarith only [h7085, h7541, hlam]
                    · linarith only [h6885, h7540, hlam]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7551 | h7551
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7552 | h7552
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h7553 | h7553
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h7554 | h7554
                          · rcases m.htr 0 5 6 (by decide) (by decide) with h7555 | h7555
                            · linarith only [h7555, hlam, p0_0]
                            · linarith only [h7555, hc05, hc56, hlam, hphi, p0_1]
                          · linarith only [h7363, h7554, hlam]
                        · linarith only [h7245, h7553, hlam]
                      · linarith only [h7085, h7552, hlam]
                    · linarith only [h6885, h7551, hlam]
                · linarith only [h7446, hc06, hlam, p0_1]
              · linarith only [h7445, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h7564 | h7564
    · linarith only [h7564, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h7566 | h7566
      · linarith only [h7566, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h7568 | h7568
        · rcases p0_3 (m.d 3 6) (by simp) with h7569 | h7569
          · rcases p0_3 (m.d 4 6) (by simp) with h7570 | h7570
            · rcases p0_3 (m.d 5 6) (by simp) with h7571 | h7571
              · rcases h6emax with h7572 | h7572 | h7572 | h7572 | h7572 | h7572
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7573 | h7573
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7574 | h7574
                    · linarith only [h7564, h7574, hlam]
                    · linarith only [h7574, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7577 | h7577
                    · linarith only [h7564, h7577, hlam]
                    · linarith only [h7577, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7580 | h7580
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7581 | h7581
                    · linarith only [h7564, h7581, hlam]
                    · linarith only [h7581, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7584 | h7584
                    · linarith only [h7564, h7584, hlam]
                    · linarith only [h7584, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7568, h7572, hc16, hlam, p0_1]
                · linarith only [h7569, h7572, hc16, hlam, p0_1]
                · linarith only [h7570, h7572, hc16, hlam, p0_1]
                · linarith only [h7572, hc16, hlam, p0_1]
              · linarith only [h7571, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7592 | h7592
              · rcases h6emax with h7593 | h7593 | h7593 | h7593 | h7593 | h7593
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7594 | h7594
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7595 | h7595
                    · linarith only [h7564, h7595, hlam]
                    · linarith only [h7594, h7595, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7598 | h7598
                    · linarith only [h7564, h7598, hlam]
                    · linarith only [h7598, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7601 | h7601
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7602 | h7602
                    · linarith only [h7564, h7602, hlam]
                    · linarith only [h7601, h7602, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7605 | h7605
                    · linarith only [h7564, h7605, hlam]
                    · linarith only [h7605, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7568, h7593, hc16, hlam, p0_1]
                · linarith only [h7569, h7593, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7610 | h7610
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7611 | h7611
                    · linarith only [h7564, h7611, hlam]
                    · linarith only [h7611, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7614 | h7614
                    · linarith only [h7564, h7614, hlam]
                    · linarith only [h7614, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7593, hc16, hlam, p0_1]
              · linarith only [h7592, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h7619 | h7619
            · rcases p0_3 (m.d 5 6) (by simp) with h7620 | h7620
              · rcases h6emax with h7621 | h7621 | h7621 | h7621 | h7621 | h7621
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7622 | h7622
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7623 | h7623
                    · linarith only [h7564, h7623, hlam]
                    · linarith only [h7623, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7626 | h7626
                    · linarith only [h7564, h7626, hlam]
                    · linarith only [h7626, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7629 | h7629
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7630 | h7630
                    · linarith only [h7564, h7630, hlam]
                    · linarith only [h7629, h7630, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7633 | h7633
                    · linarith only [h7564, h7633, hlam]
                    · linarith only [h7633, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7568, h7621, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7637 | h7637
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7638 | h7638
                    · linarith only [h7564, h7638, hlam]
                    · linarith only [h7638, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7641 | h7641
                    · linarith only [h7564, h7641, hlam]
                    · linarith only [h7641, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7619, h7621, hc16, hlam, p0_1]
                · linarith only [h7621, hc16, hlam, p0_1]
              · linarith only [h7620, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7647 | h7647
              · rcases h6emax with h7648 | h7648 | h7648 | h7648 | h7648 | h7648
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7649 | h7649
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7650 | h7650
                    · linarith only [h7564, h7650, hlam]
                    · linarith only [h7650, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7653 | h7653
                    · linarith only [h7564, h7653, hlam]
                    · linarith only [h7653, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7656 | h7656
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7657 | h7657
                    · linarith only [h7564, h7657, hlam]
                    · linarith only [h7657, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7660 | h7660
                    · linarith only [h7564, h7660, hlam]
                    · linarith only [h7660, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7568, h7648, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7664 | h7664
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7665 | h7665
                    · linarith only [h7564, h7665, hlam]
                    · linarith only [h7665, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7668 | h7668
                    · linarith only [h7564, h7668, hlam]
                    · linarith only [h7668, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7671 | h7671
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7672 | h7672
                    · linarith only [h7564, h7672, hlam]
                    · linarith only [h7671, h7672, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7675 | h7675
                    · linarith only [h7564, h7675, hlam]
                    · linarith only [h7675, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7648, hc16, hlam, p0_1]
              · linarith only [h7647, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h7680 | h7680
          · rcases p0_3 (m.d 4 6) (by simp) with h7681 | h7681
            · rcases p0_3 (m.d 5 6) (by simp) with h7682 | h7682
              · rcases h6emax with h7683 | h7683 | h7683 | h7683 | h7683 | h7683
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7684 | h7684
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7685 | h7685
                    · linarith only [h7564, h7685, hlam]
                    · linarith only [h7684, h7685, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7688 | h7688
                    · linarith only [h7564, h7688, hlam]
                    · linarith only [h7688, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7691 | h7691
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7692 | h7692
                    · linarith only [h7564, h7692, hlam]
                    · linarith only [h7691, h7692, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7695 | h7695
                    · linarith only [h7564, h7695, hlam]
                    · linarith only [h7695, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7698 | h7698
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7699 | h7699
                    · linarith only [h7564, h7699, hlam]
                    · linarith only [h7699, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7702 | h7702
                    · linarith only [h7564, h7702, hlam]
                    · linarith only [h7702, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7680, h7683, hc16, hlam, p0_1]
                · linarith only [h7681, h7683, hc16, hlam, p0_1]
                · linarith only [h7683, hc16, hlam, p0_1]
              · linarith only [h7682, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7709 | h7709
              · rcases h6emax with h7710 | h7710 | h7710 | h7710 | h7710 | h7710
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7711 | h7711
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7712 | h7712
                    · linarith only [h7564, h7712, hlam]
                    · linarith only [h7711, h7712, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7715 | h7715
                    · linarith only [h7564, h7715, hlam]
                    · linarith only [h7715, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7718 | h7718
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7719 | h7719
                    · linarith only [h7564, h7719, hlam]
                    · linarith only [h7718, h7719, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7722 | h7722
                    · linarith only [h7564, h7722, hlam]
                    · linarith only [h7722, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7725 | h7725
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7726 | h7726
                    · linarith only [h7564, h7726, hlam]
                    · linarith only [h7726, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7729 | h7729
                    · linarith only [h7564, h7729, hlam]
                    · linarith only [h7729, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7680, h7710, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7733 | h7733
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7734 | h7734
                    · linarith only [h7564, h7734, hlam]
                    · linarith only [h7733, h7734, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7737 | h7737
                    · linarith only [h7564, h7737, hlam]
                    · linarith only [h7737, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7710, hc16, hlam, p0_1]
              · linarith only [h7709, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h7742 | h7742
            · rcases p0_3 (m.d 5 6) (by simp) with h7743 | h7743
              · rcases h6emax with h7744 | h7744 | h7744 | h7744 | h7744 | h7744
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7745 | h7745
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7746 | h7746
                    · linarith only [h7564, h7746, hlam]
                    · linarith only [h7745, h7746, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7749 | h7749
                    · linarith only [h7564, h7749, hlam]
                    · linarith only [h7749, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7752 | h7752
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7753 | h7753
                    · linarith only [h7564, h7753, hlam]
                    · linarith only [h7752, h7753, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7756 | h7756
                    · linarith only [h7564, h7756, hlam]
                    · linarith only [h7756, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7759 | h7759
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7760 | h7760
                    · linarith only [h7564, h7760, hlam]
                    · linarith only [h7760, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7763 | h7763
                    · linarith only [h7564, h7763, hlam]
                    · linarith only [h7763, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7766 | h7766
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7767 | h7767
                    · linarith only [h7564, h7767, hlam]
                    · linarith only [h7767, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7770 | h7770
                    · linarith only [h7564, h7770, hlam]
                    · linarith only [h7770, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7742, h7744, hc16, hlam, p0_1]
                · linarith only [h7744, hc16, hlam, p0_1]
              · linarith only [h7743, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7776 | h7776
              · rcases h6emax with h7777 | h7777 | h7777 | h7777 | h7777 | h7777
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7778 | h7778
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7779 | h7779
                    · linarith only [h7564, h7779, hlam]
                    · linarith only [h7779, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7782 | h7782
                    · linarith only [h7564, h7782, hlam]
                    · linarith only [h7782, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7785 | h7785
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7786 | h7786
                    · linarith only [h7564, h7786, hlam]
                    · linarith only [h7786, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7789 | h7789
                    · linarith only [h7564, h7789, hlam]
                    · linarith only [h7789, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7792 | h7792
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7793 | h7793
                    · linarith only [h7564, h7793, hlam]
                    · linarith only [h7793, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7796 | h7796
                    · linarith only [h7564, h7796, hlam]
                    · linarith only [h7796, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7799 | h7799
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7800 | h7800
                    · linarith only [h7564, h7800, hlam]
                    · linarith only [h7799, h7800, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7803 | h7803
                    · linarith only [h7564, h7803, hlam]
                    · linarith only [h7803, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7806 | h7806
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7807 | h7807
                    · linarith only [h7564, h7807, hlam]
                    · linarith only [h7807, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7810 | h7810
                    · linarith only [h7564, h7810, hlam]
                    · linarith only [h7810, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7777, hc16, hlam, p0_1]
              · linarith only [h7776, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h7815 | h7815
    · linarith only [h7815, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h7817 | h7817
      · rcases p0_3 (m.d 2 6) (by simp) with h7818 | h7818
        · linarith only [h7818, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h7820 | h7820
          · rcases p0_3 (m.d 4 6) (by simp) with h7821 | h7821
            · rcases p0_3 (m.d 5 6) (by simp) with h7822 | h7822
              · rcases h6emax with h7823 | h7823 | h7823 | h7823 | h7823 | h7823
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7824 | h7824
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7825 | h7825
                    · linarith only [h7817, h7825, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7825, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7828 | h7828
                    · linarith only [h7815, h7817, h7828, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7828, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7817, h7823, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7832 | h7832
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7833 | h7833
                    · linarith only [h7815, h7817, h7833, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7832, h7833, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7836 | h7836
                    · linarith only [h7815, h7817, h7836, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7836, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7820, h7823, hc06, hlam, p0_1]
                · linarith only [h7815, h7821, h7823, hc06, hlam, p0_1]
                · linarith only [h7815, h7823, hc06, hlam, p0_1]
              · linarith only [h7822, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7843 | h7843
              · rcases h6emax with h7844 | h7844 | h7844 | h7844 | h7844 | h7844
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7845 | h7845
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7846 | h7846
                    · linarith only [h7815, h7817, h7846, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7846, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7849 | h7849
                    · linarith only [h7815, h7817, h7845, h7849, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h7815, h7817, h7849, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7817, h7844, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7853 | h7853
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7854 | h7854
                    · linarith only [h7815, h7817, h7854, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7854, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7857 | h7857
                    · linarith only [h7815, h7817, h7853, h7857, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h7815, h7817, h7857, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7820, h7844, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7861 | h7861
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7862 | h7862
                    · linarith only [h7815, h7817, h7862, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7862, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7865 | h7865
                    · linarith only [h7815, h7817, h7861, h7865, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h7815, h7817, h7865, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7844, hc06, hlam, p0_1]
              · linarith only [h7843, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h7870 | h7870
            · rcases p0_3 (m.d 5 6) (by simp) with h7871 | h7871
              · rcases h6emax with h7872 | h7872 | h7872 | h7872 | h7872 | h7872
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7873 | h7873
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7874 | h7874
                    · linarith only [h7815, h7817, h7874, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7874, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7877 | h7877
                    · linarith only [h7815, h7817, h7873, h7877, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h7815, h7817, h7877, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7817, h7872, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7881 | h7881
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7882 | h7882
                    · linarith only [h7815, h7817, h7882, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7882, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7885 | h7885
                    · linarith only [h7815, h7817, h7881, h7885, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h7815, h7817, h7885, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7888 | h7888
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7889 | h7889
                    · linarith only [h7815, h7817, h7889, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7889, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7892 | h7892
                    · linarith only [h7815, h7817, h7892, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7892, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7870, h7872, hc06, hlam, p0_1]
                · linarith only [h7815, h7872, hc06, hlam, p0_1]
              · linarith only [h7871, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7898 | h7898
              · rcases h6emax with h7899 | h7899 | h7899 | h7899 | h7899 | h7899
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7900 | h7900
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7901 | h7901
                    · linarith only [h7815, h7817, h7901, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7899, h7900, h7901, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7904 | h7904
                    · linarith only [h7815, h7817, h7904, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7904, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7817, h7899, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7908 | h7908
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7909 | h7909
                    · linarith only [h7815, h7817, h7909, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7908, h7909, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7912 | h7912
                    · linarith only [h7815, h7817, h7908, h7912, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h7815, h7817, h7912, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7915 | h7915
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7916 | h7916
                    · linarith only [h7815, h7817, h7916, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7916, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7919 | h7919
                    · linarith only [h7815, h7817, h7915, h7919, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h7815, h7817, h7919, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7922 | h7922
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7923 | h7923
                    · linarith only [h7815, h7817, h7923, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7922, h7923, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7926 | h7926
                    · linarith only [h7815, h7817, h7926, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h7815, h7817, h7926, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h7815, h7899, hc06, hlam, p0_1]
              · linarith only [h7898, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h7931 | h7931
        · linarith only [h7931, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h7933 | h7933
          · rcases p0_3 (m.d 4 6) (by simp) with h7934 | h7934
            · rcases p0_3 (m.d 5 6) (by simp) with h7935 | h7935
              · rcases h6emax with h7936 | h7936 | h7936 | h7936 | h7936 | h7936
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7937 | h7937
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7938 | h7938
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7939 | h7939
                      · linarith only [h7815, h7939, hlam]
                      · linarith only [h7939, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h7938, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7943 | h7943
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7944 | h7944
                      · linarith only [h7815, h7944, hlam]
                      · linarith only [h7937, h7943, h7944, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7817, h7943, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7948 | h7948
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7949 | h7949
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7950 | h7950
                      · linarith only [h7815, h7950, hlam]
                      · linarith only [h7948, h7950, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7936, h7948, h7949, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7954 | h7954
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7955 | h7955
                      · linarith only [h7815, h7955, hlam]
                      · linarith only [h7948, h7955, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h7936, h7954, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7959 | h7959
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7960 | h7960
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7961 | h7961
                      · linarith only [h7815, h7961, hlam]
                      · linarith only [h7961, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h7960, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7965 | h7965
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7966 | h7966
                      · linarith only [h7815, h7966, hlam]
                      · linarith only [h7959, h7965, h7966, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7817, h7965, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7817, h7933, h7936, hc16, hlam, p0_1]
                · linarith only [h7817, h7934, h7936, hc16, hlam, p0_1]
                · linarith only [h7817, h7936, hc16, hlam, p0_1]
              · linarith only [h7935, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h7974 | h7974
              · rcases h6emax with h7975 | h7975 | h7975 | h7975 | h7975 | h7975
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7976 | h7976
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7977 | h7977
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7978 | h7978
                      · linarith only [h7815, h7978, hlam]
                      · linarith only [h7978, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h7976, h7977, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7982 | h7982
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7983 | h7983
                      · linarith only [h7815, h7983, hlam]
                      · linarith only [h7976, h7983, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h7982, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7987 | h7987
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7988 | h7988
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7989 | h7989
                      · linarith only [h7815, h7989, hlam]
                      · linarith only [h7989, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7975, h7988, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7993 | h7993
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h7994 | h7994
                      · linarith only [h7815, h7994, hlam]
                      · linarith only [h7987, h7993, h7994, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7975, h7993, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h7998 | h7998
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h7999 | h7999
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8000 | h8000
                      · linarith only [h7815, h8000, hlam]
                      · linarith only [h8000, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h7999, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8004 | h8004
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8005 | h8005
                      · linarith only [h7815, h8005, hlam]
                      · linarith only [h7998, h8004, h8005, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7817, h8004, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7817, h7933, h7975, hc16, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8010 | h8010
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8011 | h8011
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8012 | h8012
                      · linarith only [h7815, h8012, hlam]
                      · linarith only [h8010, h8012, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8010, h8011, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8016 | h8016
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8017 | h8017
                      · linarith only [h7815, h8017, hlam]
                      · linarith only [h8010, h8017, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8016, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7817, h7975, hc16, hlam, p0_1]
              · linarith only [h7974, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8023 | h8023
            · rcases p0_3 (m.d 5 6) (by simp) with h8024 | h8024
              · rcases h6emax with h8025 | h8025 | h8025 | h8025 | h8025 | h8025
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8026 | h8026
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8027 | h8027
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8028 | h8028
                      · linarith only [h7815, h8028, hlam]
                      · linarith only [h8028, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8027, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8032 | h8032
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8033 | h8033
                      · linarith only [h7815, h8033, hlam]
                      · linarith only [h8026, h8032, h8033, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7817, h8032, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8037 | h8037
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8038 | h8038
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8039 | h8039
                      · linarith only [h7815, h8039, hlam]
                      · linarith only [h8039, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8025, h8037, h8038, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8043 | h8043
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8044 | h8044
                      · linarith only [h7815, h8044, hlam]
                      · linarith only [h8037, h8044, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8025, h8043, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8048 | h8048
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8049 | h8049
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8050 | h8050
                      · linarith only [h7815, h8050, hlam]
                      · linarith only [h8050, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8049, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8054 | h8054
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8055 | h8055
                      · linarith only [h7815, h8055, hlam]
                      · linarith only [h8048, h8054, h8055, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7817, h8054, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8059 | h8059
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8060 | h8060
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8061 | h8061
                      · linarith only [h7815, h8061, hlam]
                      · linarith only [h8061, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8059, h8060, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8065 | h8065
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8066 | h8066
                      · linarith only [h7815, h8066, hlam]
                      · linarith only [h8059, h8065, h8066, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7817, h8065, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7817, h8023, h8025, hc16, hlam, p0_1]
                · linarith only [h7817, h8025, hc16, hlam, p0_1]
              · linarith only [h8024, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8073 | h8073
              · rcases h6emax with h8074 | h8074 | h8074 | h8074 | h8074 | h8074
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8075 | h8075
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8076 | h8076
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8077 | h8077
                      · linarith only [h7815, h8077, hlam]
                      · linarith only [h8075, h8077, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8075, h8076, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8081 | h8081
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8082 | h8082
                      · linarith only [h7815, h8082, hlam]
                      · linarith only [h8075, h8082, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8081, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8086 | h8086
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8087 | h8087
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8088 | h8088
                      · linarith only [h7815, h8088, hlam]
                      · linarith only [h8088, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8074, h8086, h8087, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8092 | h8092
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8093 | h8093
                      · linarith only [h7815, h8093, hlam]
                      · linarith only [h8086, h8093, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8074, h8092, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8097 | h8097
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8098 | h8098
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8099 | h8099
                      · linarith only [h7815, h8099, hlam]
                      · linarith only [h8099, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8098, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8103 | h8103
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8104 | h8104
                      · linarith only [h7815, h8104, hlam]
                      · linarith only [h8097, h8103, h8104, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h7817, h8103, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8108 | h8108
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8109 | h8109
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8110 | h8110
                      · linarith only [h7815, h8110, hlam]
                      · linarith only [h8110, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8108, h8109, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8114 | h8114
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8115 | h8115
                      · linarith only [h7815, h8115, hlam]
                      · linarith only [h8108, h8115, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8114, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8119 | h8119
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8120 | h8120
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8121 | h8121
                      · linarith only [h7815, h8121, hlam]
                      · linarith only [h8121, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8119, h8120, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8125 | h8125
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8126 | h8126
                      · linarith only [h7815, h8126, hlam]
                      · linarith only [h8119, h8126, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h7817, h8125, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h7817, h8074, hc16, hlam, p0_1]
              · linarith only [h8073, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h8132 | h8132
    · linarith only [h8132, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h8134 | h8134
      · rcases p0_3 (m.d 2 6) (by simp) with h8135 | h8135
        · rcases p0_3 (m.d 3 6) (by simp) with h8136 | h8136
          · linarith only [h8136, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8138 | h8138
            · rcases p0_3 (m.d 5 6) (by simp) with h8139 | h8139
              · rcases h6emax with h8140 | h8140 | h8140 | h8140 | h8140 | h8140
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8141 | h8141
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8142 | h8142
                    · linarith only [h8134, h8142, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8142, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8145 | h8145
                    · linarith only [h8132, h8134, h8145, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8145, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8134, h8140, hc06, hlam, p0_1]
                · linarith only [h8132, h8135, h8140, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8150 | h8150
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8151 | h8151
                    · linarith only [h8132, h8134, h8151, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8150, h8151, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8154 | h8154
                    · linarith only [h8132, h8134, h8154, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8154, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8138, h8140, hc06, hlam, p0_1]
                · linarith only [h8132, h8140, hc06, hlam, p0_1]
              · linarith only [h8139, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8160 | h8160
              · rcases h6emax with h8161 | h8161 | h8161 | h8161 | h8161 | h8161
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8162 | h8162
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8163 | h8163
                    · linarith only [h8132, h8134, h8163, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8161, h8162, h8163, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8166 | h8166
                    · linarith only [h8132, h8134, h8162, h8166, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8132, h8134, h8166, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8134, h8161, hc06, hlam, p0_1]
                · linarith only [h8132, h8135, h8161, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8171 | h8171
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8172 | h8172
                    · linarith only [h8132, h8134, h8172, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8172, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8175 | h8175
                    · linarith only [h8132, h8134, h8171, h8175, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8132, h8134, h8175, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8178 | h8178
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8179 | h8179
                    · linarith only [h8132, h8134, h8179, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8179, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8182 | h8182
                    · linarith only [h8132, h8134, h8178, h8182, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8132, h8134, h8182, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8161, hc06, hlam, p0_1]
              · linarith only [h8160, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h8187 | h8187
          · linarith only [h8187, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8189 | h8189
            · rcases p0_3 (m.d 5 6) (by simp) with h8190 | h8190
              · rcases h6emax with h8191 | h8191 | h8191 | h8191 | h8191 | h8191
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8192 | h8192
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8193 | h8193
                    · linarith only [h8134, h8135, h8193, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8191, h8192, h8193, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8196 | h8196
                    · linarith only [h8134, h8135, h8196, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8196, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8134, h8191, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8200 | h8200
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8201 | h8201
                    · linarith only [h8132, h8134, h8201, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8200, h8201, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8204 | h8204
                    · linarith only [h8132, h8134, h8204, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8204, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8207 | h8207
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8208 | h8208
                    · linarith only [h8132, h8134, h8208, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8208, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8211 | h8211
                    · linarith only [h8132, h8134, h8211, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8211, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8189, h8191, hc06, hlam, p0_1]
                · linarith only [h8132, h8191, hc06, hlam, p0_1]
              · linarith only [h8190, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8217 | h8217
              · rcases h6emax with h8218 | h8218 | h8218 | h8218 | h8218 | h8218
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8219 | h8219
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8220 | h8220
                    · linarith only [h8132, h8134, h8220, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8218, h8219, h8220, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8223 | h8223
                    · linarith only [h8132, h8134, h8223, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8223, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8134, h8218, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8227 | h8227
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8228 | h8228
                    · linarith only [h8132, h8134, h8228, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8227, h8228, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8231 | h8231
                    · linarith only [h8132, h8134, h8231, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8231, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8234 | h8234
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8235 | h8235
                    · linarith only [h8132, h8134, h8235, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8235, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8238 | h8238
                    · linarith only [h8132, h8134, h8234, h8238, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8132, h8134, h8238, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8241 | h8241
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8242 | h8242
                    · linarith only [h8132, h8134, h8242, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8241, h8242, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8245 | h8245
                    · linarith only [h8132, h8134, h8245, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8132, h8134, h8245, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8132, h8218, hc06, hlam, p0_1]
              · linarith only [h8217, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h8250 | h8250
        · rcases p0_3 (m.d 3 6) (by simp) with h8251 | h8251
          · linarith only [h8251, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8253 | h8253
            · rcases p0_3 (m.d 5 6) (by simp) with h8254 | h8254
              · rcases h6emax with h8255 | h8255 | h8255 | h8255 | h8255 | h8255
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8256 | h8256
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8257 | h8257
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8258 | h8258
                      · linarith only [h8132, h8250, h8256, h8257, h8258, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h8132, h8250, h8258, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h8134, h8257, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8262 | h8262
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8263 | h8263
                      · linarith only [h8132, h8250, h8263, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8250, h8263, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h8134, h8262, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8267 | h8267
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8268 | h8268
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8269 | h8269
                      · linarith only [h8132, h8250, h8268, h8269, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8269, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8255, h8267, h8268, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8273 | h8273
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8274 | h8274
                      · linarith only [h8132, h8250, h8273, h8274, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8274, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8255, h8273, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h8132, h8250, h8255, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8279 | h8279
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8280 | h8280
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8281 | h8281
                      · linarith only [h8132, h8250, h8280, h8281, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8281, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8280, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8285 | h8285
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8286 | h8286
                      · linarith only [h8132, h8250, h8285, h8286, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8286, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8285, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8132, h8253, h8255, hc06, hlam, p0_1]
                · linarith only [h8132, h8255, hc06, hlam, p0_1]
              · linarith only [h8254, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8293 | h8293
              · rcases h6emax with h8294 | h8294 | h8294 | h8294 | h8294 | h8294
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8295 | h8295
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8296 | h8296
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8297 | h8297
                      · linarith only [h8132, h8250, h8296, h8297, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8250, h8297, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h8134, h8296, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8301 | h8301
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8302 | h8302
                      · linarith only [h8132, h8250, h8301, h8302, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8302, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8301, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8306 | h8306
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8307 | h8307
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8308 | h8308
                      · linarith only [h8132, h8250, h8308, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8308, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8294, h8307, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8312 | h8312
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8313 | h8313
                      · linarith only [h8132, h8250, h8312, h8313, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8313, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8294, h8312, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h8132, h8250, h8294, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8318 | h8318
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8319 | h8319
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8320 | h8320
                      · linarith only [h8132, h8250, h8319, h8320, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8320, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8318, h8319, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8324 | h8324
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8325 | h8325
                      · linarith only [h8132, h8250, h8324, h8325, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8325, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8324, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8329 | h8329
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8330 | h8330
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8331 | h8331
                      · linarith only [h8132, h8250, h8330, h8331, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8331, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8330, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8335 | h8335
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8336 | h8336
                      · linarith only [h8132, h8250, h8335, h8336, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8132, h8336, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8335, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8132, h8294, hc06, hlam, p0_1]
              · linarith only [h8293, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h8342 | h8342
          · linarith only [h8342, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8344 | h8344
            · rcases p0_3 (m.d 5 6) (by simp) with h8345 | h8345
              · rcases h6emax with h8346 | h8346 | h8346 | h8346 | h8346 | h8346
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8347 | h8347
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8348 | h8348
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8349 | h8349
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8350 | h8350
                        · linarith only [h8132, h8350, hlam]
                        · linarith only [h8350, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8349, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8347, h8348, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8355 | h8355
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8356 | h8356
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8357 | h8357
                        · linarith only [h8132, h8357, hlam]
                        · linarith only [h8357, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8347, h8356, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8355, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8362 | h8362
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8363 | h8363
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8364 | h8364
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8365 | h8365
                        · linarith only [h8132, h8365, hlam]
                        · linarith only [h8365, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8364, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8346, h8362, h8363, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8370 | h8370
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8371 | h8371
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8372 | h8372
                        · linarith only [h8132, h8372, hlam]
                        · linarith only [h8372, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8362, h8371, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8346, h8370, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8377 | h8377
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8378 | h8378
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8379 | h8379
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8380 | h8380
                        · linarith only [h8132, h8380, hlam]
                        · linarith only [h8380, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8346, h8379, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h8134, h8378, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8385 | h8385
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8386 | h8386
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8387 | h8387
                        · linarith only [h8132, h8387, hlam]
                        · linarith only [h8387, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8346, h8377, h8385, h8386, hc16, hlam]
                    · linarith only [h8134, h8385, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8392 | h8392
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8393 | h8393
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8394 | h8394
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8395 | h8395
                        · linarith only [h8132, h8395, hlam]
                        · linarith only [h8395, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8394, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8392, h8393, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8400 | h8400
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8401 | h8401
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8402 | h8402
                        · linarith only [h8132, h8402, hlam]
                        · linarith only [h8402, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8392, h8400, h8401, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h8134, h8400, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8134, h8344, h8346, hc16, hlam, p0_1]
                · linarith only [h8134, h8346, hc16, hlam, p0_1]
              · linarith only [h8345, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8410 | h8410
              · rcases h6emax with h8411 | h8411 | h8411 | h8411 | h8411 | h8411
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8412 | h8412
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8413 | h8413
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8414 | h8414
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8415 | h8415
                        · linarith only [h8132, h8415, hlam]
                        · linarith only [h8415, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8414, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8412, h8413, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8420 | h8420
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8421 | h8421
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8422 | h8422
                        · linarith only [h8132, h8422, hlam]
                        · linarith only [h8422, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8412, h8420, h8421, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h8134, h8420, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8427 | h8427
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8428 | h8428
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8429 | h8429
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8430 | h8430
                        · linarith only [h8132, h8430, hlam]
                        · linarith only [h8430, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8429, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8411, h8427, h8428, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8435 | h8435
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8436 | h8436
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8437 | h8437
                        · linarith only [h8132, h8437, hlam]
                        · linarith only [h8437, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8427, h8435, h8436, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h8411, h8435, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8442 | h8442
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8443 | h8443
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8444 | h8444
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8445 | h8445
                        · linarith only [h8132, h8445, hlam]
                        · linarith only [h8445, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8411, h8444, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h8134, h8443, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8450 | h8450
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8451 | h8451
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8452 | h8452
                        · linarith only [h8132, h8452, hlam]
                        · linarith only [h8452, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8411, h8442, h8450, h8451, hc16, hlam]
                    · linarith only [h8134, h8450, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8457 | h8457
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8458 | h8458
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8459 | h8459
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8460 | h8460
                        · linarith only [h8132, h8460, hlam]
                        · linarith only [h8460, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8459, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8457, h8458, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8465 | h8465
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8466 | h8466
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8467 | h8467
                        · linarith only [h8132, h8467, hlam]
                        · linarith only [h8467, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8457, h8465, h8466, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h8134, h8465, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8472 | h8472
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8473 | h8473
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8474 | h8474
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8475 | h8475
                        · linarith only [h8132, h8475, hlam]
                        · linarith only [h8475, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8474, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8472, h8473, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8480 | h8480
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8481 | h8481
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8482 | h8482
                        · linarith only [h8132, h8482, hlam]
                        · linarith only [h8482, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8250, h8472, h8481, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8134, h8480, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8134, h8411, hc16, hlam, p0_1]
              · linarith only [h8410, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h8489 | h8489
    · linarith only [h8489, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · rcases p0_3 (m.d 1 6) (by simp) with h8491 | h8491
      · rcases p0_3 (m.d 2 6) (by simp) with h8492 | h8492
        · rcases p0_3 (m.d 3 6) (by simp) with h8493 | h8493
          · rcases p0_3 (m.d 4 6) (by simp) with h8494 | h8494
            · linarith only [h8494, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8496 | h8496
              · rcases h6emax with h8497 | h8497 | h8497 | h8497 | h8497 | h8497
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8498 | h8498
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8499 | h8499
                    · linarith only [h8491, h8499, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8499, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8502 | h8502
                    · linarith only [h8489, h8491, h8502, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8502, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8491, h8497, hc06, hlam, p0_1]
                · linarith only [h8489, h8492, h8497, hc06, hlam, p0_1]
                · linarith only [h8489, h8493, h8497, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8508 | h8508
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8509 | h8509
                    · linarith only [h8489, h8491, h8509, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8508, h8509, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8512 | h8512
                    · linarith only [h8489, h8491, h8512, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8512, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8497, hc06, hlam, p0_1]
              · linarith only [h8496, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8517 | h8517
            · linarith only [h8517, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8519 | h8519
              · rcases h6emax with h8520 | h8520 | h8520 | h8520 | h8520 | h8520
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8521 | h8521
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8522 | h8522
                    · linarith only [h8489, h8491, h8522, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8522, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8525 | h8525
                    · linarith only [h8489, h8491, h8521, h8525, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8525, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8491, h8520, hc06, hlam, p0_1]
                · linarith only [h8489, h8492, h8520, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8530 | h8530
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8531 | h8531
                    · linarith only [h8489, h8491, h8531, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8530, h8531, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8534 | h8534
                    · linarith only [h8489, h8491, h8530, h8534, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8534, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8537 | h8537
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8538 | h8538
                    · linarith only [h8489, h8491, h8538, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8538, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8541 | h8541
                    · linarith only [h8489, h8491, h8537, h8541, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8541, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8520, hc06, hlam, p0_1]
              · linarith only [h8519, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h8546 | h8546
          · rcases p0_3 (m.d 4 6) (by simp) with h8547 | h8547
            · linarith only [h8547, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8549 | h8549
              · rcases h6emax with h8550 | h8550 | h8550 | h8550 | h8550 | h8550
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8551 | h8551
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8552 | h8552
                    · linarith only [h8489, h8491, h8552, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8552, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8555 | h8555
                    · linarith only [h8489, h8491, h8551, h8555, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8555, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8491, h8550, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8559 | h8559
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8560 | h8560
                    · linarith only [h8489, h8491, h8560, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8560, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8563 | h8563
                    · linarith only [h8489, h8491, h8559, h8563, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8563, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8546, h8550, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8567 | h8567
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8568 | h8568
                    · linarith only [h8489, h8491, h8568, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8568, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8571 | h8571
                    · linarith only [h8489, h8491, h8567, h8571, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8571, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8550, hc06, hlam, p0_1]
              · linarith only [h8549, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8576 | h8576
            · linarith only [h8576, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8578 | h8578
              · rcases h6emax with h8579 | h8579 | h8579 | h8579 | h8579 | h8579
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8580 | h8580
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8581 | h8581
                    · linarith only [h8489, h8491, h8581, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8581, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8584 | h8584
                    · linarith only [h8489, h8491, h8580, h8584, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8584, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8491, h8579, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8588 | h8588
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8589 | h8589
                    · linarith only [h8489, h8491, h8589, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8589, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8592 | h8592
                    · linarith only [h8489, h8491, h8588, h8592, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8592, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8595 | h8595
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8596 | h8596
                    · linarith only [h8489, h8491, h8596, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8595, h8596, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8599 | h8599
                    · linarith only [h8489, h8491, h8595, h8599, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8599, hc01, hc16, hlam, hphi, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8602 | h8602
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8603 | h8603
                    · linarith only [h8489, h8491, h8603, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                    · linarith only [h8489, h8491, h8603, hc01, hc16, hlam, hphi, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8606 | h8606
                    · linarith only [h8489, h8491, h8602, h8606, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                    · linarith only [h8489, h8491, h8606, hc01, hc16, hlam, hphi, p0_1]
                · linarith only [h8489, h8579, hc06, hlam, p0_1]
              · linarith only [h8578, hlam, p0_0]
      · rcases p0_3 (m.d 2 6) (by simp) with h8611 | h8611
        · rcases p0_3 (m.d 3 6) (by simp) with h8612 | h8612
          · rcases p0_3 (m.d 4 6) (by simp) with h8613 | h8613
            · linarith only [h8613, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8615 | h8615
              · rcases h6emax with h8616 | h8616 | h8616 | h8616 | h8616 | h8616
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8617 | h8617
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8618 | h8618
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8619 | h8619
                      · linarith only [h8489, h8611, h8617, h8618, h8619, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
                      · linarith only [h8489, h8619, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8617, h8618, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8623 | h8623
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8624 | h8624
                      · linarith only [h8489, h8611, h8623, h8624, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8624, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8623, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8628 | h8628
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8629 | h8629
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8630 | h8630
                      · linarith only [h8489, h8611, h8629, h8630, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8630, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8616, h8629, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8634 | h8634
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8635 | h8635
                      · linarith only [h8489, h8611, h8634, h8635, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8635, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8616, h8634, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h8489, h8611, h8616, hc06, hlam, p0_1]
                · linarith only [h8489, h8612, h8616, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8641 | h8641
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8642 | h8642
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8643 | h8643
                      · linarith only [h8489, h8611, h8642, h8643, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8643, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8642, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8647 | h8647
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8648 | h8648
                      · linarith only [h8489, h8611, h8647, h8648, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8648, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8647, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8489, h8616, hc06, hlam, p0_1]
              · linarith only [h8615, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8654 | h8654
            · linarith only [h8654, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8656 | h8656
              · rcases h6emax with h8657 | h8657 | h8657 | h8657 | h8657 | h8657
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8658 | h8658
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8659 | h8659
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8660 | h8660
                      · linarith only [h8489, h8611, h8659, h8660, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8611, h8660, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h8491, h8659, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8664 | h8664
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8665 | h8665
                      · linarith only [h8489, h8611, h8664, h8665, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8665, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8664, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8669 | h8669
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8670 | h8670
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8671 | h8671
                      · linarith only [h8489, h8611, h8671, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8671, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8657, h8669, h8670, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8675 | h8675
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8676 | h8676
                      · linarith only [h8489, h8611, h8675, h8676, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8676, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8657, h8675, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · linarith only [h8489, h8611, h8657, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8681 | h8681
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8682 | h8682
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8683 | h8683
                      · linarith only [h8489, h8611, h8682, h8683, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8683, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8682, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8687 | h8687
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8688 | h8688
                      · linarith only [h8489, h8611, h8687, h8688, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8688, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8687, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8692 | h8692
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8693 | h8693
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8694 | h8694
                      · linarith only [h8489, h8611, h8694, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8611, h8694, hc02, hc26, hlam, hphi, p0_1]
                    · linarith only [h8491, h8693, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8698 | h8698
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8699 | h8699
                      · linarith only [h8489, h8611, h8698, h8699, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo1]
                      · linarith only [h8489, h8699, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8698, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8489, h8657, hc06, hlam, p0_1]
              · linarith only [h8656, hlam, p0_0]
        · rcases p0_3 (m.d 3 6) (by simp) with h8705 | h8705
          · rcases p0_3 (m.d 4 6) (by simp) with h8706 | h8706
            · linarith only [h8706, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8708 | h8708
              · rcases h6emax with h8709 | h8709 | h8709 | h8709 | h8709 | h8709
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8710 | h8710
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8711 | h8711
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8712 | h8712
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8713 | h8713
                        · linarith only [h8489, h8705, h8711, h8713, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8705, h8713, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h8611, h8712, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8710, h8711, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8718 | h8718
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8719 | h8719
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8720 | h8720
                        · linarith only [h8489, h8705, h8720, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8705, h8720, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h8611, h8710, h8718, h8719, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h8491, h8718, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8725 | h8725
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8726 | h8726
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8727 | h8727
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8728 | h8728
                        · linarith only [h8489, h8705, h8728, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8705, h8728, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h8611, h8727, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8709, h8725, h8726, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8733 | h8733
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8734 | h8734
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8735 | h8735
                        · linarith only [h8489, h8705, h8733, h8735, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8735, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8611, h8725, h8733, h8734, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h8709, h8733, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8740 | h8740
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8741 | h8741
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8742 | h8742
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8743 | h8743
                        · linarith only [h8489, h8705, h8743, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8705, h8743, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h8709, h8742, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h8491, h8741, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8748 | h8748
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8749 | h8749
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8750 | h8750
                        · linarith only [h8489, h8705, h8748, h8750, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8750, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8709, h8740, h8748, h8749, hc16, hlam]
                    · linarith only [h8491, h8748, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8489, h8705, h8709, hc06, hlam, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8756 | h8756
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8757 | h8757
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8758 | h8758
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8759 | h8759
                        · linarith only [h8489, h8705, h8757, h8759, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8705, h8759, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h8611, h8758, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8756, h8757, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8764 | h8764
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8765 | h8765
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8766 | h8766
                        · linarith only [h8489, h8705, h8766, hc06, hlam, hphi, ht0b, ht6b, p0_1, u0elo2]
                        · linarith only [h8489, h8705, h8766, hc03, hc36, hlam, hphi, p0_1]
                      · linarith only [h8611, h8756, h8765, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8764, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8489, h8709, hc06, hlam, p0_1]
              · linarith only [h8708, hlam, p0_0]
          · rcases p0_3 (m.d 4 6) (by simp) with h8773 | h8773
            · linarith only [h8773, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h8775 | h8775
              · rcases h6emax with h8776 | h8776 | h8776 | h8776 | h8776 | h8776
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8777 | h8777
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8778 | h8778
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8779 | h8779
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8780 | h8780
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8781 | h8781
                          · linarith only [h8489, h8781, hlam]
                          · linarith only [h8781, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8780, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8611, h8779, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8778, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8787 | h8787
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8788 | h8788
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8789 | h8789
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8790 | h8790
                          · linarith only [h8489, h8790, hlam]
                          · linarith only [h8790, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8789, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8611, h8777, h8787, h8788, hc16, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1]
                    · linarith only [h8491, h8787, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8796 | h8796
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8797 | h8797
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8798 | h8798
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8799 | h8799
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8800 | h8800
                          · linarith only [h8489, h8800, hlam]
                          · linarith only [h8800, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8799, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8611, h8798, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8776, h8796, h8797, hc12, hlam, ht23, ht34, ht45, ht56]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8806 | h8806
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8807 | h8807
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8808 | h8808
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8809 | h8809
                          · linarith only [h8489, h8809, hlam]
                          · linarith only [h8809, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8808, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8611, h8796, h8807, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8776, h8806, hc01, hlam, ht12, ht23, ht34, ht45, ht56]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8815 | h8815
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8816 | h8816
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8817 | h8817
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8818 | h8818
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8819 | h8819
                          · linarith only [h8489, h8819, hlam]
                          · linarith only [h8819, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8818, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8776, h8817, hc02, hlam, ht23, ht34, ht45, ht56]
                    · linarith only [h8491, h8815, h8816, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8825 | h8825
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8826 | h8826
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8827 | h8827
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8828 | h8828
                          · linarith only [h8489, h8828, hlam]
                          · linarith only [h8828, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8827, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8776, h8815, h8825, h8826, hc16, hlam]
                    · linarith only [h8491, h8825, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8834 | h8834
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8835 | h8835
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8836 | h8836
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8837 | h8837
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8838 | h8838
                          · linarith only [h8489, h8838, hlam]
                          · linarith only [h8838, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8776, h8837, hc03, hlam, ht34, ht45, ht56]
                      · linarith only [h8611, h8836, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8834, h8835, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8844 | h8844
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8845 | h8845
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8846 | h8846
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8847 | h8847
                          · linarith only [h8489, h8847, hlam]
                          · linarith only [h8847, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8776, h8846, hc03, hlam, ht34, ht45, ht56]
                      · linarith only [h8611, h8834, h8845, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8844, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · rcases m.htr 0 1 2 (by decide) (by decide) with h8853 | h8853
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8854 | h8854
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8855 | h8855
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8856 | h8856
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8857 | h8857
                          · linarith only [h8489, h8857, hlam]
                          · linarith only [h8857, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8856, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8611, h8855, hc02, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8853, h8854, hc12, hc56, hlam, hphi, ht23, ht34, ht45, p0_1]
                  · rcases m.htr 0 1 6 (by decide) (by decide) with h8863 | h8863
                    · rcases m.htr 0 2 6 (by decide) (by decide) with h8864 | h8864
                      · rcases m.htr 0 3 6 (by decide) (by decide) with h8865 | h8865
                        · rcases m.htr 0 4 6 (by decide) (by decide) with h8866 | h8866
                          · linarith only [h8489, h8866, hlam]
                          · linarith only [h8866, hc04, hc56, hlam, hphi, ht45, p0_1]
                        · linarith only [h8705, h8865, hc03, hc56, hlam, hphi, ht34, ht45, p0_1]
                      · linarith only [h8611, h8853, h8864, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                    · linarith only [h8491, h8863, hc01, hc56, hlam, hphi, ht12, ht23, ht34, ht45, p0_1]
                · linarith only [h8491, h8776, hc16, hlam, p0_1]
              · linarith only [h8775, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
