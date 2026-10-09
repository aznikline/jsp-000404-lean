import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6346000 in
theorem n8l_sBT8_H_I_H_R (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0bigk := hb0.1
  have h6ehi := hb6.1
  have u6ehi0 := h6ehi (m.d 0 6) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 0 6) (by simp) with h8 | h8
              · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h5, hlam]
                  · linarith only [h10, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h9, hlam, p0_0]
              · linarith only [h8, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
              · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
                · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h5, hlam]
                  · linarith only [h17, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h16, hlam, p0_0]
              · linarith only [h15, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 0 6) (by simp) with h23 | h23
              · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                  · linarith only [h25, h5, hlam]
                  · linarith only [h25, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h24, hlam, p0_0]
              · linarith only [h23, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h30 | h30
              · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
                · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
                  · linarith only [h32, h5, hlam]
                  · linarith only [h32, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h31, hlam, p0_0]
              · linarith only [h30, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h37 | h37
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · rcases p0_3 (m.d 0 6) (by simp) with h39 | h39
              · rcases m.htr 0 1 2 (by decide) (by decide) with h40 | h40
                · rcases m.htr 0 1 3 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
                    · linarith only [h37, h42, hlam]
                    · linarith only [h42, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h40, h41, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h40, hlam, p0_0]
              · linarith only [h39, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h48 | h48
              · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
                · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h37, h51, hlam]
                    · linarith only [h51, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h49, h50, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h49, hlam, p0_0]
              · linarith only [h48, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h57 | h57
            · rcases p0_3 (m.d 0 6) (by simp) with h58 | h58
              · rcases m.htr 0 1 2 (by decide) (by decide) with h59 | h59
                · rcases m.htr 0 1 3 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h57, h62, hlam]
                      · linarith only [h62, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h59, h61, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h59, h60, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h59, hlam, p0_0]
              · linarith only [h58, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h69 | h69
              · rcases m.htr 0 1 2 (by decide) (by decide) with h70 | h70
                · rcases m.htr 0 1 3 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h74 | h74
                        · linarith only [h69, h74, hlam]
                        · linarith only [h74, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h70, h73, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h70, h72, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h70, h71, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h70, hlam, p0_0]
              · linarith only [h69, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h83 | h83
    · rcases p0_3 (m.d 0 2) (by simp) with h84 | h84
      · rcases p0_3 (m.d 0 3) (by simp) with h85 | h85
        · linarith only [h85, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h87 | h87
          · rcases p0_3 (m.d 0 5) (by simp) with h88 | h88
            · rcases p0_3 (m.d 0 6) (by simp) with h89 | h89
              · rcases m.htr 0 1 2 (by decide) (by decide) with h90 | h90
                · linarith only [h84, h90, hlam]
                · linarith only [h90, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h89, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h94 | h94
              · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
                · linarith only [h84, h95, hlam]
                · linarith only [h95, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h94, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h99 | h99
            · rcases p0_3 (m.d 0 6) (by simp) with h100 | h100
              · rcases m.htr 0 1 2 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h84, hlam]
                · linarith only [h101, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h100, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h105 | h105
              · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
                · linarith only [h106, h84, hlam]
                · linarith only [h106, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h105, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h110 | h110
        · linarith only [h110, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
          · rcases p0_3 (m.d 0 5) (by simp) with h113 | h113
            · rcases p0_3 (m.d 0 6) (by simp) with h114 | h114
              · rcases m.htr 0 1 2 (by decide) (by decide) with h115 | h115
                · rcases m.htr 0 1 3 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h117 | h117
                    · linarith only [h112, h117, hlam]
                    · linarith only [h117, h84, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h116, hlam, p0_0]
                · linarith only [h115, h84, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h114, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h123 | h123
              · rcases m.htr 0 1 2 (by decide) (by decide) with h124 | h124
                · rcases m.htr 0 1 3 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h126 | h126
                    · linarith only [h112, h126, hlam]
                    · linarith only [h126, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h125, hlam, p0_0]
                · linarith only [h124, h84, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h123, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h132 | h132
            · rcases p0_3 (m.d 0 6) (by simp) with h133 | h133
              · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
                · rcases m.htr 0 1 3 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h137 | h137
                      · linarith only [h132, h137, hlam]
                      · linarith only [h137, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h134, h136, h84, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h135, hlam, p0_0]
                · linarith only [h134, h84, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h133, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h144 | h144
              · rcases m.htr 0 1 2 (by decide) (by decide) with h145 | h145
                · rcases m.htr 0 1 3 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h149 | h149
                        · linarith only [h144, h149, hlam]
                        · linarith only [h149, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h145, h148, h84, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h145, h147, h84, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h146, hlam, p0_0]
                · linarith only [h145, h84, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h144, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h83, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h158 | h158
    · rcases p0_3 (m.d 0 2) (by simp) with h159 | h159
      · rcases p0_3 (m.d 0 3) (by simp) with h160 | h160
        · rcases p0_3 (m.d 0 4) (by simp) with h161 | h161
          · linarith only [h161, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h163 | h163
            · rcases p0_3 (m.d 0 6) (by simp) with h164 | h164
              · rcases m.htr 0 1 2 (by decide) (by decide) with h165 | h165
                · linarith only [h159, h165, hlam]
                · linarith only [h165, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h164, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h169 | h169
              · rcases m.htr 0 1 2 (by decide) (by decide) with h170 | h170
                · linarith only [h159, h170, hlam]
                · linarith only [h170, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h169, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h174 | h174
          · linarith only [h174, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h176 | h176
            · rcases p0_3 (m.d 0 6) (by simp) with h177 | h177
              · rcases m.htr 0 1 2 (by decide) (by decide) with h178 | h178
                · linarith only [h159, h178, hlam]
                · linarith only [h160, h178, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h177, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h182 | h182
              · rcases m.htr 0 1 2 (by decide) (by decide) with h183 | h183
                · linarith only [h159, h183, hlam]
                · linarith only [h183, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h182, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h187 | h187
        · rcases p0_3 (m.d 0 4) (by simp) with h188 | h188
          · linarith only [h188, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h190 | h190
            · rcases p0_3 (m.d 0 6) (by simp) with h191 | h191
              · rcases m.htr 0 1 2 (by decide) (by decide) with h192 | h192
                · rcases m.htr 0 1 3 (by decide) (by decide) with h193 | h193
                  · linarith only [h187, h193, hlam]
                  · linarith only [h159, h193, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h159, h192, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h191, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h198 | h198
              · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
                · rcases m.htr 0 1 3 (by decide) (by decide) with h200 | h200
                  · linarith only [h187, h200, hlam]
                  · linarith only [h200, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h159, h199, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h198, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h205 | h205
          · linarith only [h205, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h207 | h207
            · rcases p0_3 (m.d 0 6) (by simp) with h208 | h208
              · rcases m.htr 0 1 2 (by decide) (by decide) with h209 | h209
                · rcases m.htr 0 1 3 (by decide) (by decide) with h210 | h210
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
                      · linarith only [h207, h212, hlam]
                      · linarith only [h187, h212, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h211, hlam, p0_0]
                  · linarith only [h159, h209, h210, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h159, h209, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h208, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h219 | h219
              · rcases m.htr 0 1 2 (by decide) (by decide) with h220 | h220
                · rcases m.htr 0 1 3 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h223 | h223
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h224 | h224
                        · linarith only [h219, h224, hlam]
                        · linarith only [h224, hc04, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h159, h220, h223, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h222, hlam, p0_0]
                  · linarith only [h159, h220, h221, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h159, h220, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h219, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h158, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h233 | h233
    · rcases p0_3 (m.d 0 2) (by simp) with h234 | h234
      · rcases p0_3 (m.d 0 3) (by simp) with h235 | h235
        · rcases p0_3 (m.d 0 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 0 5) (by simp) with h237 | h237
            · linarith only [h237, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h239 | h239
              · rcases m.htr 0 1 2 (by decide) (by decide) with h240 | h240
                · linarith only [h234, h240, hlam]
                · linarith only [h240, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h239, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h244 | h244
            · linarith only [h244, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h246 | h246
              · rcases m.htr 0 1 2 (by decide) (by decide) with h247 | h247
                · linarith only [h234, h247, hlam]
                · linarith only [h236, h247, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h246, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h251 | h251
          · rcases p0_3 (m.d 0 5) (by simp) with h252 | h252
            · linarith only [h252, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h254 | h254
              · rcases m.htr 0 1 2 (by decide) (by decide) with h255 | h255
                · linarith only [h234, h255, hlam]
                · linarith only [h235, h255, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h254, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h259 | h259
            · linarith only [h259, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h261 | h261
              · rcases m.htr 0 1 2 (by decide) (by decide) with h262 | h262
                · linarith only [h234, h262, hlam]
                · linarith only [h251, h262, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h261, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h266 | h266
        · rcases p0_3 (m.d 0 4) (by simp) with h267 | h267
          · rcases p0_3 (m.d 0 5) (by simp) with h268 | h268
            · linarith only [h268, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h270 | h270
              · rcases m.htr 0 1 2 (by decide) (by decide) with h271 | h271
                · rcases m.htr 0 1 3 (by decide) (by decide) with h272 | h272
                  · linarith only [h266, h272, hlam]
                  · linarith only [h234, h272, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h234, h271, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h270, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h277 | h277
            · linarith only [h277, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h279 | h279
              · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
                · rcases m.htr 0 1 3 (by decide) (by decide) with h281 | h281
                  · linarith only [h266, h281, hlam]
                  · linarith only [h267, h281, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h234, h280, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h279, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h286 | h286
          · rcases p0_3 (m.d 0 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h289 | h289
              · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
                · rcases m.htr 0 1 3 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h292 | h292
                    · linarith only [h286, h292, hlam]
                    · linarith only [h266, h292, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h234, h290, h291, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h234, h290, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h289, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h300 | h300
              · rcases m.htr 0 1 2 (by decide) (by decide) with h301 | h301
                · rcases m.htr 0 1 3 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h303 | h303
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h304 | h304
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h305 | h305
                        · linarith only [h300, h305, hlam]
                        · linarith only [h266, h305, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h304, hlam, p0_0]
                    · linarith only [h234, h301, h303, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h234, h301, h302, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h234, h301, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h300, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h233, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h315 | h315
    · linarith only [h315, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h317 | h317
      · rcases p0_3 (m.d 0 3) (by simp) with h318 | h318
        · rcases p0_3 (m.d 0 4) (by simp) with h319 | h319
          · rcases p0_3 (m.d 0 5) (by simp) with h320 | h320
            · rcases p0_3 (m.d 0 6) (by simp) with h321 | h321
              · rcases m.htr 0 1 2 (by decide) (by decide) with h322 | h322
                · linarith only [h322, hlam, p0_0]
                · linarith only [h322, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h321, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h326 | h326
              · rcases m.htr 0 1 2 (by decide) (by decide) with h327 | h327
                · linarith only [h327, hlam, p0_0]
                · linarith only [h327, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h326, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h331 | h331
            · rcases p0_3 (m.d 0 6) (by simp) with h332 | h332
              · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
                · linarith only [h333, hlam, p0_0]
                · linarith only [h333, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h332, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h337 | h337
              · rcases m.htr 0 1 2 (by decide) (by decide) with h338 | h338
                · linarith only [h338, hlam, p0_0]
                · linarith only [h338, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h337, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h342 | h342
          · rcases p0_3 (m.d 0 5) (by simp) with h343 | h343
            · rcases p0_3 (m.d 0 6) (by simp) with h344 | h344
              · rcases m.htr 0 1 2 (by decide) (by decide) with h345 | h345
                · linarith only [h345, hlam, p0_0]
                · linarith only [h345, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h344, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h349 | h349
              · rcases m.htr 0 1 2 (by decide) (by decide) with h350 | h350
                · linarith only [h350, hlam, p0_0]
                · linarith only [h350, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h349, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h354 | h354
            · rcases p0_3 (m.d 0 6) (by simp) with h355 | h355
              · rcases m.htr 0 1 2 (by decide) (by decide) with h356 | h356
                · linarith only [h356, hlam, p0_0]
                · linarith only [h356, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h355, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h360 | h360
              · rcases m.htr 0 1 2 (by decide) (by decide) with h361 | h361
                · linarith only [h361, hlam, p0_0]
                · linarith only [h361, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h360, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h317, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h367 | h367
    · rcases p0_3 (m.d 0 2) (by simp) with h368 | h368
      · rcases p0_3 (m.d 0 3) (by simp) with h369 | h369
        · linarith only [h369, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h371 | h371
          · rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
            · rcases p0_3 (m.d 0 6) (by simp) with h373 | h373
              · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
                · rcases m.htr 0 1 3 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h377 | h377
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h378 | h378
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h379 | h379
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h380 | h380
                            · linarith only [h371, h380, hlam]
                            · linarith only [h380, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h379, hlam, p0_0]
                        · linarith only [h374, h375, h378, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h374, h375, h377, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h374, h375, h376, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h374, h375, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h374, hlam]
              · linarith only [h373, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h390 | h390
              · rcases m.htr 0 1 2 (by decide) (by decide) with h391 | h391
                · rcases m.htr 0 1 3 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h393 | h393
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h395 | h395
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h396 | h396
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h397 | h397
                            · linarith only [h371, h397, hlam]
                            · linarith only [h397, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h396, hlam, p0_0]
                        · linarith only [h391, h392, h395, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h391, h392, h394, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h391, h392, h393, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h391, h392, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h391, hlam]
              · linarith only [h390, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h407 | h407
            · rcases p0_3 (m.d 0 6) (by simp) with h408 | h408
              · rcases m.htr 0 1 2 (by decide) (by decide) with h409 | h409
                · rcases m.htr 0 1 3 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h411 | h411
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h412 | h412
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h413 | h413
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h414 | h414
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h415 | h415
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h416 | h416
                              · linarith only [h407, h416, hlam]
                              · linarith only [h416, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h410, h415, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h414, hlam, p0_0]
                        · linarith only [h409, h410, h413, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h409, h410, h412, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h409, h410, h411, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h409, h410, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h409, hlam]
              · linarith only [h408, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h427 | h427
              · rcases m.htr 0 1 2 (by decide) (by decide) with h428 | h428
                · rcases m.htr 0 1 3 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h431 | h431
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h432 | h432
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h433 | h433
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h434 | h434
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h435 | h435
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h436 | h436
                                · linarith only [h427, h436, hlam]
                                · linarith only [h436, hc03, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h429, h435, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h429, h434, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h433, hlam, p0_0]
                        · linarith only [h428, h429, h432, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h428, h429, h431, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h428, h429, h430, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h428, h429, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h428, hlam]
              · linarith only [h367, h427, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h368, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h449 | h449
      · rcases p0_3 (m.d 0 3) (by simp) with h450 | h450
        · linarith only [h450, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h452 | h452
          · rcases p0_3 (m.d 0 5) (by simp) with h453 | h453
            · rcases p0_3 (m.d 0 6) (by simp) with h454 | h454
              · rcases m.htr 0 1 2 (by decide) (by decide) with h455 | h455
                · linarith only [h367, h455, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h455, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h454, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h459 | h459
              · rcases m.htr 0 1 2 (by decide) (by decide) with h460 | h460
                · linarith only [h367, h460, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h460, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h459, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h464 | h464
            · rcases p0_3 (m.d 0 6) (by simp) with h465 | h465
              · rcases m.htr 0 1 2 (by decide) (by decide) with h466 | h466
                · linarith only [h367, h466, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h466, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h465, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h470 | h470
              · rcases m.htr 0 1 2 (by decide) (by decide) with h471 | h471
                · linarith only [h367, h471, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h367, h471, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h470, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h449, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h476 | h476
    · rcases p0_3 (m.d 0 2) (by simp) with h477 | h477
      · rcases p0_3 (m.d 0 3) (by simp) with h478 | h478
        · rcases p0_3 (m.d 0 4) (by simp) with h479 | h479
          · linarith only [h479, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h481 | h481
            · rcases p0_3 (m.d 0 6) (by simp) with h482 | h482
              · rcases m.htr 0 1 2 (by decide) (by decide) with h483 | h483
                · rcases m.htr 0 1 3 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h485 | h485
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h486 | h486
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h487 | h487
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h488 | h488
                          · linarith only [h478, h488, hlam]
                          · linarith only [h485, h488, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h483, h485, h487, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h483, h485, h486, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h483, h485, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h483, h484, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h483, hlam]
              · linarith only [h482, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h497 | h497
              · rcases m.htr 0 1 2 (by decide) (by decide) with h498 | h498
                · rcases m.htr 0 1 3 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h503 | h503
                          · linarith only [h478, h503, hlam]
                          · linarith only [h503, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h498, h500, h502, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h498, h500, h501, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h498, h500, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h498, h499, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h498, hlam]
              · linarith only [h497, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h512 | h512
          · linarith only [h512, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h514 | h514
            · rcases p0_3 (m.d 0 6) (by simp) with h515 | h515
              · rcases m.htr 0 1 2 (by decide) (by decide) with h516 | h516
                · rcases m.htr 0 1 3 (by decide) (by decide) with h517 | h517
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h518 | h518
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h519 | h519
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h520 | h520
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h521 | h521
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h522 | h522
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h523 | h523
                              · linarith only [h514, h523, hlam]
                              · linarith only [h478, h523, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h522, hlam, p0_0]
                          · linarith only [h478, h517, h521, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h478, h516, h517, h520, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h478, h516, h517, h519, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h478, h516, h517, h518, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h478, h516, h517, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h516, hlam]
              · linarith only [h515, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h534 | h534
              · rcases m.htr 0 1 2 (by decide) (by decide) with h535 | h535
                · rcases m.htr 0 1 3 (by decide) (by decide) with h536 | h536
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h537 | h537
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h538 | h538
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h540 | h540
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h541 | h541
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h542 | h542
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h543 | h543
                                · linarith only [h534, h543, hlam]
                                · linarith only [h543, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h478, h536, h542, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h541, hlam, p0_0]
                          · linarith only [h478, h536, h540, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h478, h535, h536, h539, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h478, h535, h536, h538, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h478, h535, h536, h537, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h478, h535, h536, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h535, hlam]
              · linarith only [h534, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h477, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h556 | h556
      · rcases p0_3 (m.d 0 3) (by simp) with h557 | h557
        · rcases p0_3 (m.d 0 4) (by simp) with h558 | h558
          · linarith only [h558, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h560 | h560
            · rcases p0_3 (m.d 0 6) (by simp) with h561 | h561
              · rcases m.htr 0 1 2 (by decide) (by decide) with h562 | h562
                · linarith only [h476, h562, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h562, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h561, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h566 | h566
              · rcases m.htr 0 1 2 (by decide) (by decide) with h567 | h567
                · linarith only [h476, h567, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h567, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h566, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h571 | h571
          · linarith only [h571, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h573 | h573
            · rcases p0_3 (m.d 0 6) (by simp) with h574 | h574
              · rcases m.htr 0 1 2 (by decide) (by decide) with h575 | h575
                · linarith only [h476, h575, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h575, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h574, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h579 | h579
              · rcases m.htr 0 1 2 (by decide) (by decide) with h580 | h580
                · linarith only [h476, h580, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h476, h580, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h579, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h556, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h585 | h585
    · rcases p0_3 (m.d 0 2) (by simp) with h586 | h586
      · rcases p0_3 (m.d 0 3) (by simp) with h587 | h587
        · rcases p0_3 (m.d 0 4) (by simp) with h588 | h588
          · rcases p0_3 (m.d 0 5) (by simp) with h589 | h589
            · linarith only [h589, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h591 | h591
              · rcases m.htr 0 1 2 (by decide) (by decide) with h592 | h592
                · rcases m.htr 0 1 3 (by decide) (by decide) with h593 | h593
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h594 | h594
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h595 | h595
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h596 | h596
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h597 | h597
                          · linarith only [h587, h597, hlam]
                          · linarith only [h597, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h592, h595, h596, hc15, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h592, h595, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h592, h594, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h592, h593, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h585, h592, hlam]
              · linarith only [h591, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h606 | h606
            · linarith only [h606, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h608 | h608
              · rcases m.htr 0 1 2 (by decide) (by decide) with h609 | h609
                · rcases m.htr 0 1 3 (by decide) (by decide) with h610 | h610
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h611 | h611
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h612 | h612
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h613 | h613
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h614 | h614
                          · linarith only [h587, h614, hlam]
                          · linarith only [h588, h614, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h588, h609, h611, h613, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h588, h609, h611, h612, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h588, h609, h611, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h588, h609, h610, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h585, h609, hlam]
              · linarith only [h608, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h623 | h623
          · rcases p0_3 (m.d 0 5) (by simp) with h624 | h624
            · linarith only [h624, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h626 | h626
              · rcases m.htr 0 1 2 (by decide) (by decide) with h627 | h627
                · rcases m.htr 0 1 3 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h629 | h629
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h630 | h630
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h631 | h631
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h632 | h632
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h633 | h633
                            · linarith only [h623, h633, hlam]
                            · linarith only [h587, h633, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h587, h628, h632, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h587, h627, h628, h631, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h587, h627, h628, h630, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h587, h627, h628, h629, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h587, h627, h628, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h585, h627, hlam]
              · linarith only [h585, h626, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h643 | h643
            · linarith only [h643, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h645 | h645
              · rcases m.htr 0 1 2 (by decide) (by decide) with h646 | h646
                · rcases m.htr 0 1 3 (by decide) (by decide) with h647 | h647
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h648 | h648
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h649 | h649
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h650 | h650
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h651 | h651
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h652 | h652
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h653 | h653
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h654 | h654
                                · linarith only [h645, h654, hlam]
                                · linarith only [h623, h654, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h653, hlam, p0_0]
                            · linarith only [h587, h647, h652, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h587, h647, h651, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h587, h646, h647, h650, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h587, h646, h647, h649, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h587, h646, h647, h648, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h587, h646, h647, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h585, h646, hlam]
              · linarith only [h645, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h586, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h667 | h667
      · rcases p0_3 (m.d 0 3) (by simp) with h668 | h668
        · rcases p0_3 (m.d 0 4) (by simp) with h669 | h669
          · rcases p0_3 (m.d 0 5) (by simp) with h670 | h670
            · linarith only [h670, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h672 | h672
              · rcases m.htr 0 1 2 (by decide) (by decide) with h673 | h673
                · linarith only [h585, h673, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h585, h673, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h672, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h677 | h677
            · linarith only [h677, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h679 | h679
              · rcases m.htr 0 1 2 (by decide) (by decide) with h680 | h680
                · linarith only [h585, h680, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h585, h680, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h679, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h684 | h684
          · rcases p0_3 (m.d 0 5) (by simp) with h685 | h685
            · linarith only [h685, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h687 | h687
              · rcases m.htr 0 1 2 (by decide) (by decide) with h688 | h688
                · linarith only [h585, h688, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h585, h688, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h687, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h692 | h692
            · linarith only [h692, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h694 | h694
              · rcases m.htr 0 1 2 (by decide) (by decide) with h695 | h695
                · linarith only [h585, h695, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h585, h695, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h694, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h667, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h701 | h701
    · linarith only [h701, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h703 | h703
      · rcases p0_3 (m.d 0 3) (by simp) with h704 | h704
        · rcases p0_3 (m.d 0 4) (by simp) with h705 | h705
          · rcases p0_3 (m.d 0 5) (by simp) with h706 | h706
            · rcases p0_3 (m.d 0 6) (by simp) with h707 | h707
              · rcases m.htr 0 1 2 (by decide) (by decide) with h708 | h708
                · linarith only [h708, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h708, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h703, h707, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h712 | h712
              · rcases m.htr 0 1 2 (by decide) (by decide) with h713 | h713
                · linarith only [h703, h713, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h713, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h703, h712, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h717 | h717
            · rcases p0_3 (m.d 0 6) (by simp) with h718 | h718
              · rcases m.htr 0 1 2 (by decide) (by decide) with h719 | h719
                · linarith only [h703, h719, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h719, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h703, h718, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h723 | h723
              · rcases m.htr 0 1 2 (by decide) (by decide) with h724 | h724
                · linarith only [h703, h724, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h724, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h703, h723, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h704, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h729 | h729
        · rcases p0_3 (m.d 0 4) (by simp) with h730 | h730
          · rcases p0_3 (m.d 0 5) (by simp) with h731 | h731
            · rcases p0_3 (m.d 0 6) (by simp) with h732 | h732
              · rcases m.htr 0 1 2 (by decide) (by decide) with h733 | h733
                · linarith only [h733, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h733, hlam]
              · linarith only [h732, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h737 | h737
              · rcases m.htr 0 1 2 (by decide) (by decide) with h738 | h738
                · linarith only [h738, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h738, hlam]
              · linarith only [h737, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h742 | h742
            · rcases p0_3 (m.d 0 6) (by simp) with h743 | h743
              · rcases m.htr 0 1 2 (by decide) (by decide) with h744 | h744
                · linarith only [h744, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h744, hlam]
              · linarith only [h743, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h748 | h748
              · rcases m.htr 0 1 2 (by decide) (by decide) with h749 | h749
                · linarith only [h749, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h703, h749, hlam]
              · linarith only [h748, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h729, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h754 | h754
    · rcases p0_3 (m.d 0 2) (by simp) with h755 | h755
      · linarith only [h755, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h757 | h757
        · rcases p0_3 (m.d 0 4) (by simp) with h758 | h758
          · rcases p0_3 (m.d 0 5) (by simp) with h759 | h759
            · rcases p0_3 (m.d 0 6) (by simp) with h760 | h760
              · rcases m.htr 0 1 2 (by decide) (by decide) with h761 | h761
                · rcases m.htr 0 1 3 (by decide) (by decide) with h762 | h762
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h763 | h763
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h764 | h764
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h765 | h765
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h766 | h766
                          · linarith only [h766, hlam, p0_0]
                          · linarith only [h766, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h761, h762, h765, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h761, h762, h764, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h761, h762, h763, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h754, h762, hlam]
                · linarith only [h754, h761, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h754, h760, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h775 | h775
              · rcases m.htr 0 1 2 (by decide) (by decide) with h776 | h776
                · rcases m.htr 0 1 3 (by decide) (by decide) with h777 | h777
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h778 | h778
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h779 | h779
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h780 | h780
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h781 | h781
                          · linarith only [h781, hlam, p0_0]
                          · linarith only [h781, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h776, h777, h780, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h776, h777, h779, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h776, h777, h778, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h754, h777, hlam]
                · linarith only [h754, h776, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h754, h775, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h790 | h790
            · rcases p0_3 (m.d 0 6) (by simp) with h791 | h791
              · rcases m.htr 0 1 2 (by decide) (by decide) with h792 | h792
                · rcases m.htr 0 1 3 (by decide) (by decide) with h793 | h793
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h794 | h794
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h795 | h795
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h796 | h796
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h797 | h797
                          · linarith only [h797, hlam, p0_0]
                          · linarith only [h797, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h792, h793, h796, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h792, h793, h795, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h792, h793, h794, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h754, h793, hlam]
                · linarith only [h754, h792, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h754, h791, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h806 | h806
              · rcases m.htr 0 1 2 (by decide) (by decide) with h807 | h807
                · rcases m.htr 0 1 3 (by decide) (by decide) with h808 | h808
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h809 | h809
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h810 | h810
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h811 | h811
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h812 | h812
                          · linarith only [h812, hlam, p0_0]
                          · linarith only [h812, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h807, h808, h811, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h807, h808, h810, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h807, h808, h809, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h754, h808, hlam]
                · linarith only [h754, h807, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h754, h806, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h757, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h822 | h822
      · linarith only [h822, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h824 | h824
        · rcases p0_3 (m.d 0 4) (by simp) with h825 | h825
          · rcases p0_3 (m.d 0 5) (by simp) with h826 | h826
            · rcases p0_3 (m.d 0 6) (by simp) with h827 | h827
              · rcases m.htr 0 1 2 (by decide) (by decide) with h828 | h828
                · linarith only [h754, h828, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h830 | h830
                  · linarith only [h828, h830, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h828, h830, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h827, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h834 | h834
              · rcases m.htr 0 1 2 (by decide) (by decide) with h835 | h835
                · linarith only [h754, h835, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h837 | h837
                  · linarith only [h835, h837, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h835, h837, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h834, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h841 | h841
            · rcases p0_3 (m.d 0 6) (by simp) with h842 | h842
              · rcases m.htr 0 1 2 (by decide) (by decide) with h843 | h843
                · linarith only [h754, h843, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h845 | h845
                  · linarith only [h843, h845, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h843, h845, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h842, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h849 | h849
              · rcases m.htr 0 1 2 (by decide) (by decide) with h850 | h850
                · linarith only [h754, h850, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h852 | h852
                  · linarith only [h850, h852, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h850, h852, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h849, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h824, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h858 | h858
    · rcases p0_3 (m.d 0 2) (by simp) with h859 | h859
      · rcases p0_3 (m.d 0 3) (by simp) with h860 | h860
        · rcases p0_3 (m.d 0 4) (by simp) with h861 | h861
          · linarith only [h861, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h863 | h863
            · rcases p0_3 (m.d 0 6) (by simp) with h864 | h864
              · rcases m.htr 0 1 2 (by decide) (by decide) with h865 | h865
                · rcases m.htr 0 1 3 (by decide) (by decide) with h866 | h866
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h867 | h867
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h868 | h868
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h869 | h869
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h870 | h870
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h871 | h871
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h872 | h872
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h873 | h873
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h874 | h874
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h875 | h875
                                    · linarith only [h863, h875, hlam]
                                    · linarith only [h867, h875, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h874, hlam, p0_0]
                                · linarith only [h867, h870, h873, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h867, h870, h872, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h867, h870, h871, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h859, h870, hlam]
                        · linarith only [h866, h867, h869, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h866, h867, h868, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h866, h867, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h866, hlam]
                · linarith only [h858, h865, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h858, h864, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h889 | h889
              · rcases m.htr 0 1 2 (by decide) (by decide) with h890 | h890
                · rcases m.htr 0 1 3 (by decide) (by decide) with h891 | h891
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h892 | h892
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h893 | h893
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h894 | h894
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h895 | h895
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h896 | h896
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h897 | h897
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h898 | h898
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h899 | h899
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h900 | h900
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h901 | h901
                                      · linarith only [h889, h901, hlam]
                                      · linarith only [h901, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                    · linarith only [h892, h900, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h899, hlam, p0_0]
                                · linarith only [h892, h895, h898, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h892, h895, h897, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h892, h895, h896, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h859, h895, hlam]
                        · linarith only [h891, h892, h894, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h891, h892, h893, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h891, h892, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h891, hlam]
                · linarith only [h858, h890, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h858, h889, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h860, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h917 | h917
        · rcases p0_3 (m.d 0 4) (by simp) with h918 | h918
          · linarith only [h918, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h920 | h920
            · rcases p0_3 (m.d 0 6) (by simp) with h921 | h921
              · rcases m.htr 0 1 2 (by decide) (by decide) with h922 | h922
                · rcases m.htr 0 1 3 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h924 | h924
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h925 | h925
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h926 | h926
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h927 | h927
                          · linarith only [h859, h923, h927, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h859, h922, h927, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h859, h922, h923, h926, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h859, h922, h923, h925, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h859, h922, h923, h924, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h923, hlam]
                · linarith only [h858, h859, h922, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h858, h921, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h936 | h936
              · rcases m.htr 0 1 2 (by decide) (by decide) with h937 | h937
                · rcases m.htr 0 1 3 (by decide) (by decide) with h938 | h938
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h939 | h939
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h940 | h940
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h941 | h941
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h942 | h942
                          · linarith only [h859, h938, h942, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h859, h942, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h859, h937, h938, h941, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h859, h937, h938, h940, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h859, h937, h938, h939, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h858, h938, hlam]
                · linarith only [h858, h859, h937, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h858, h936, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h917, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h952 | h952
      · rcases p0_3 (m.d 0 3) (by simp) with h953 | h953
        · rcases p0_3 (m.d 0 4) (by simp) with h954 | h954
          · linarith only [h954, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h956 | h956
            · rcases p0_3 (m.d 0 6) (by simp) with h957 | h957
              · rcases m.htr 0 1 2 (by decide) (by decide) with h958 | h958
                · linarith only [h858, h958, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h858, h952, h958, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h952, h957, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h962 | h962
              · rcases m.htr 0 1 2 (by decide) (by decide) with h963 | h963
                · linarith only [h858, h952, h963, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h858, h952, h963, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h952, h962, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h953, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h968 | h968
        · rcases p0_3 (m.d 0 4) (by simp) with h969 | h969
          · linarith only [h969, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h971 | h971
            · rcases p0_3 (m.d 0 6) (by simp) with h972 | h972
              · rcases m.htr 0 1 2 (by decide) (by decide) with h973 | h973
                · linarith only [h858, h973, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h975 | h975
                  · linarith only [h952, h973, h975, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h952, h973, h975, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h972, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h979 | h979
              · rcases m.htr 0 1 2 (by decide) (by decide) with h980 | h980
                · linarith only [h858, h980, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h982 | h982
                  · linarith only [h952, h980, h982, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h952, h980, h982, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h979, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h968, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h987 | h987
    · rcases p0_3 (m.d 0 2) (by simp) with h988 | h988
      · rcases p0_3 (m.d 0 3) (by simp) with h989 | h989
        · rcases p0_3 (m.d 0 4) (by simp) with h990 | h990
          · rcases p0_3 (m.d 0 5) (by simp) with h991 | h991
            · linarith only [h991, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h993 | h993
              · rcases m.htr 0 1 2 (by decide) (by decide) with h994 | h994
                · rcases m.htr 0 1 3 (by decide) (by decide) with h995 | h995
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h996 | h996
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h997 | h997
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h998 | h998
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h999 | h999
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1000 | h1000
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1001 | h1001
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1002 | h1002
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1003 | h1003
                                  · linarith only [h1003, h990, hlam]
                                  · linarith only [h1003, h997, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                · linarith only [h1002, h997, h999, hc15, hc26, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                              · linarith only [h1001, h997, h999, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                            · linarith only [h1000, h997, h999, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                          · linarith only [h988, h999, hlam]
                        · linarith only [h995, h997, h998, hc15, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h995, h997, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h995, h996, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h987, h995, hlam]
                · linarith only [h987, h994, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h987, h993, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1016 | h1016
            · linarith only [h1016, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1018 | h1018
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1019 | h1019
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1020 | h1020
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1021 | h1021
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1022 | h1022
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1023 | h1023
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1024 | h1024
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1025 | h1025
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1026 | h1026
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1027 | h1027
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1028 | h1028
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1029 | h1029
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1030 | h1030
                                      · linarith only [h1018, h1030, hlam]
                                      · linarith only [h1030, h990, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                    · linarith only [h1029, hlam, p0_0]
                                  · linarith only [h1021, h1028, h990, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h1021, h1024, h1027, h990, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1021, h1024, h1026, h990, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1021, h1024, h1025, h990, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1024, h988, hlam]
                        · linarith only [h1020, h1021, h1023, h990, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1020, h1021, h1022, h990, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1020, h1021, h990, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1020, h987, hlam]
                · linarith only [h1019, h987, h990, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1018, h987, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h989, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1046 | h1046
        · rcases p0_3 (m.d 0 4) (by simp) with h1047 | h1047
          · rcases p0_3 (m.d 0 5) (by simp) with h1048 | h1048
            · linarith only [h1048, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1050 | h1050
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1051 | h1051
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1052 | h1052
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1053 | h1053
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1054 | h1054
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1055 | h1055
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1056 | h1056
                          · linarith only [h1052, h1056, h988, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1051, h1056, h988, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h1051, h1052, h1055, h988, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1051, h1052, h1054, h988, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1051, h1052, h1053, h988, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1052, h987, hlam]
                · linarith only [h1051, h987, h988, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1050, h987, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1065 | h1065
            · linarith only [h1065, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1067 | h1067
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1068 | h1068
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1069 | h1069
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1070 | h1070
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1071 | h1071
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1072 | h1072
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1073 | h1073
                          · linarith only [h1069, h1073, h988, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1073, h988, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1068, h1069, h1072, h988, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1068, h1069, h1071, h988, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1068, h1069, h1070, h988, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1069, h987, hlam]
                · linarith only [h1068, h987, h988, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1067, h987, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h1046, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1083 | h1083
      · rcases p0_3 (m.d 0 3) (by simp) with h1084 | h1084
        · rcases p0_3 (m.d 0 4) (by simp) with h1085 | h1085
          · rcases p0_3 (m.d 0 5) (by simp) with h1086 | h1086
            · linarith only [h1086, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1088 | h1088
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1089 | h1089
                · linarith only [h1089, h987, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1083, h1089, h987, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1083, h1088, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1093 | h1093
            · linarith only [h1093, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1095 | h1095
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1096 | h1096
                · linarith only [h1083, h1096, h987, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1083, h1096, h987, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1083, h1095, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h1084, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1101 | h1101
        · rcases p0_3 (m.d 0 4) (by simp) with h1102 | h1102
          · rcases p0_3 (m.d 0 5) (by simp) with h1103 | h1103
            · linarith only [h1103, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1105 | h1105
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1106 | h1106
                · linarith only [h1106, h987, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1108 | h1108
                  · linarith only [h1083, h1106, h1108, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1083, h1106, h1108, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1105, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1112 | h1112
            · linarith only [h1112, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1114 | h1114
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1115 | h1115
                · linarith only [h1115, h987, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1117 | h1117
                  · linarith only [h1083, h1115, h1117, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1083, h1115, h1117, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1114, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h1101, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1123 | h1123
    · linarith only [h1123, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1125 | h1125
      · rcases p0_3 (m.d 0 3) (by simp) with h1126 | h1126
        · rcases p0_3 (m.d 0 4) (by simp) with h1127 | h1127
          · rcases p0_3 (m.d 0 5) (by simp) with h1128 | h1128
            · rcases p0_3 (m.d 0 6) (by simp) with h1129 | h1129
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1130 | h1130
                · linarith only [h1125, h1130, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1130, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1125, h1129, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1134 | h1134
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1135 | h1135
                · linarith only [h1125, h1135, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1135, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1125, h1134, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1127, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1140 | h1140
          · rcases p0_3 (m.d 0 5) (by simp) with h1141 | h1141
            · rcases p0_3 (m.d 0 6) (by simp) with h1142 | h1142
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1143 | h1143
                · linarith only [h1125, h1143, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1143, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1125, h1142, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1147 | h1147
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1148 | h1148
                · linarith only [h1125, h1148, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1148, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1125, h1147, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1140, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1153 | h1153
        · rcases p0_3 (m.d 0 4) (by simp) with h1154 | h1154
          · rcases p0_3 (m.d 0 5) (by simp) with h1155 | h1155
            · rcases p0_3 (m.d 0 6) (by simp) with h1156 | h1156
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1157 | h1157
                · linarith only [h1157, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1157, hlam]
              · linarith only [h1156, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1161 | h1161
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1162 | h1162
                · linarith only [h1162, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1162, hlam]
              · linarith only [h1161, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1154, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1167 | h1167
          · rcases p0_3 (m.d 0 5) (by simp) with h1168 | h1168
            · rcases p0_3 (m.d 0 6) (by simp) with h1169 | h1169
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1170 | h1170
                · linarith only [h1170, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1170, hlam]
              · linarith only [h1169, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1174 | h1174
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1175 | h1175
                · linarith only [h1175, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1125, h1175, hlam]
              · linarith only [h1174, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1167, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1180 | h1180
    · rcases p0_3 (m.d 0 2) (by simp) with h1181 | h1181
      · linarith only [h1181, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1183 | h1183
        · rcases p0_3 (m.d 0 4) (by simp) with h1184 | h1184
          · rcases p0_3 (m.d 0 5) (by simp) with h1185 | h1185
            · rcases p0_3 (m.d 0 6) (by simp) with h1186 | h1186
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1187 | h1187
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1188 | h1188
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1189 | h1189
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1190 | h1190
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1191 | h1191
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1192 | h1192
                          · linarith only [h1183, h1188, h1192, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1183, h1192, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1187, h1189, h1191, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1187, h1189, h1190, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1180, h1189, hlam]
                  · linarith only [h1180, h1187, h1188, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1180, h1187, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1180, h1186, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1201 | h1201
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1202 | h1202
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1203 | h1203
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1204 | h1204
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1206 | h1206
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1207 | h1207
                          · linarith only [h1183, h1203, h1207, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1183, h1207, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1183, h1202, h1203, h1206, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1183, h1202, h1203, h1205, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1180, h1204, hlam]
                  · linarith only [h1180, h1202, h1203, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1180, h1202, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1180, h1201, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1184, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1217 | h1217
          · rcases p0_3 (m.d 0 5) (by simp) with h1218 | h1218
            · rcases p0_3 (m.d 0 6) (by simp) with h1219 | h1219
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1220 | h1220
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1221 | h1221
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1222 | h1222
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1223 | h1223
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1224 | h1224
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1225 | h1225
                          · linarith only [h1222, h1225, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1183, h1225, hlam]
                        · linarith only [h1222, h1224, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1220, h1222, h1223, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1180, h1222, hlam]
                  · linarith only [h1180, h1220, h1221, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1180, h1220, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1180, h1219, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1234 | h1234
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1235 | h1235
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1236 | h1236
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1237 | h1237
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1238 | h1238
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1239 | h1239
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1240 | h1240
                          · linarith only [h1237, h1240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1183, h1240, hlam]
                        · linarith only [h1237, h1239, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1235, h1237, h1238, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1180, h1237, hlam]
                  · linarith only [h1180, h1235, h1236, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1180, h1235, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1180, h1234, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1217, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1250 | h1250
      · linarith only [h1250, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1252 | h1252
        · rcases p0_3 (m.d 0 4) (by simp) with h1253 | h1253
          · rcases p0_3 (m.d 0 5) (by simp) with h1254 | h1254
            · rcases p0_3 (m.d 0 6) (by simp) with h1255 | h1255
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1256 | h1256
                · linarith only [h1180, h1256, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1258 | h1258
                  · linarith only [h1256, h1258, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1252, h1256, h1258, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1255, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1262 | h1262
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1263 | h1263
                · linarith only [h1180, h1263, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1265 | h1265
                  · linarith only [h1263, h1265, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1252, h1263, h1265, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1262, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1253, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1270 | h1270
          · rcases p0_3 (m.d 0 5) (by simp) with h1271 | h1271
            · rcases p0_3 (m.d 0 6) (by simp) with h1272 | h1272
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1273 | h1273
                · linarith only [h1180, h1273, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1275 | h1275
                  · linarith only [h1273, h1275, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1277 | h1277
                    · linarith only [h1273, h1277, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1273, h1277, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1272, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1281 | h1281
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1282 | h1282
                · linarith only [h1180, h1282, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1284 | h1284
                  · linarith only [h1282, h1284, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1286 | h1286
                    · linarith only [h1282, h1286, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1282, h1286, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1281, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1270, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1291 | h1291
    · rcases p0_3 (m.d 0 2) (by simp) with h1292 | h1292
      · rcases p0_3 (m.d 0 3) (by simp) with h1293 | h1293
        · linarith only [h1293, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1295 | h1295
          · rcases p0_3 (m.d 0 5) (by simp) with h1296 | h1296
            · rcases p0_3 (m.d 0 6) (by simp) with h1297 | h1297
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1298 | h1298
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1299 | h1299
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1300 | h1300
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1301 | h1301
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1302 | h1302
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1303 | h1303
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1304 | h1304
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1305 | h1305
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1306 | h1306
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1307 | h1307
                                  · linarith only [h1307, hlam, p0_0]
                                  · linarith only [h1299, h1307, hc13, hc34, hlam, hphi, p0_1]
                                · linarith only [h1299, h1304, h1306, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1299, h1304, h1305, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1292, h1304, hlam]
                          · linarith only [h1292, h1299, h1303, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1299, h1300, h1302, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1299, h1300, h1301, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1291, h1300, hlam]
                  · linarith only [h1291, h1299, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1291, h1298, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1291, h1297, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1320 | h1320
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1321 | h1321
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1322 | h1322
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1323 | h1323
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1324 | h1324
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1325 | h1325
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1326 | h1326
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1327 | h1327
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1328 | h1328
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1329 | h1329
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1330 | h1330
                                  · linarith only [h1330, hlam, p0_0]
                                  · linarith only [h1330, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h1322, h1327, h1329, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1322, h1327, h1328, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1292, h1327, hlam]
                          · linarith only [h1292, h1322, h1326, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1322, h1323, h1325, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1322, h1323, h1324, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1291, h1323, hlam]
                  · linarith only [h1291, h1322, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1291, h1321, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1291, h1320, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1295, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1344 | h1344
        · linarith only [h1344, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1346 | h1346
          · rcases p0_3 (m.d 0 5) (by simp) with h1347 | h1347
            · rcases p0_3 (m.d 0 6) (by simp) with h1348 | h1348
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1349 | h1349
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1350 | h1350
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1351 | h1351
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1352 | h1352
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1353 | h1353
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1354 | h1354
                          · linarith only [h1292, h1354, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1356 | h1356
                            · linarith only [h1351, h1354, h1356, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1349, h1354, h1356, hc12, hc24, hlam, hphi, p0_1]
                        · linarith only [h1351, h1353, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1292, h1349, h1351, h1352, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1291, h1351, hlam]
                  · linarith only [h1291, h1292, h1349, h1350, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1291, h1292, h1349, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1291, h1348, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1365 | h1365
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1366 | h1366
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1367 | h1367
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1368 | h1368
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1369 | h1369
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1370 | h1370
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1371 | h1371
                          · linarith only [h1292, h1371, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1373 | h1373
                            · linarith only [h1368, h1371, h1373, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1371, h1373, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h1368, h1370, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1292, h1366, h1368, h1369, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1291, h1368, hlam]
                  · linarith only [h1291, h1292, h1366, h1367, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1291, h1292, h1366, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1291, h1365, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1346, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1383 | h1383
      · rcases p0_3 (m.d 0 3) (by simp) with h1384 | h1384
        · linarith only [h1384, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1386 | h1386
          · rcases p0_3 (m.d 0 5) (by simp) with h1387 | h1387
            · rcases p0_3 (m.d 0 6) (by simp) with h1388 | h1388
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1389 | h1389
                · linarith only [h1291, h1389, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1291, h1383, h1389, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1383, h1388, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1393 | h1393
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1394 | h1394
                · linarith only [h1291, h1383, h1394, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1291, h1383, h1394, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1383, h1393, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1386, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1399 | h1399
        · linarith only [h1399, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1401 | h1401
          · rcases p0_3 (m.d 0 5) (by simp) with h1402 | h1402
            · rcases p0_3 (m.d 0 6) (by simp) with h1403 | h1403
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1404 | h1404
                · linarith only [h1291, h1404, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1406 | h1406
                  · linarith only [h1291, h1406, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1408 | h1408
                    · linarith only [h1383, h1404, h1408, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1383, h1404, h1408, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1403, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1412 | h1412
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1413 | h1413
                · linarith only [h1291, h1413, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1415 | h1415
                  · linarith only [h1291, h1415, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1417 | h1417
                    · linarith only [h1383, h1413, h1417, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1383, h1413, h1417, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1412, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1401, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1423 | h1423
    · rcases p0_3 (m.d 0 2) (by simp) with h1424 | h1424
      · rcases p0_3 (m.d 0 3) (by simp) with h1425 | h1425
        · rcases p0_3 (m.d 0 4) (by simp) with h1426 | h1426
          · rcases p0_3 (m.d 0 5) (by simp) with h1427 | h1427
            · linarith only [h1427, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1429 | h1429
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1430 | h1430
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1431 | h1431
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1432 | h1432
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1433 | h1433
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1434 | h1434
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1435 | h1435
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1436 | h1436
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1437 | h1437
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1438 | h1438
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1439 | h1439
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1440 | h1440
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1441 | h1441
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1442 | h1442
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h1443 | h1443
                                          · linarith only [h1429, h1443, hlam]
                                          · linarith only [h1433, h1443, hc15, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, p0_1]
                                        · linarith only [h1442, hlam, p0_0]
                                      · linarith only [h1433, h1439, h1441, hc15, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                    · linarith only [h1433, h1439, h1440, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                  · linarith only [h1425, h1439, hlam]
                                · linarith only [h1433, h1436, h1438, hc15, hc26, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                              · linarith only [h1433, h1436, h1437, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                            · linarith only [h1424, h1436, hlam]
                          · linarith only [h1424, h1433, h1435, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h1432, h1433, h1434, hc15, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h1432, h1433, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h1423, h1432, hlam]
                  · linarith only [h1424, h1430, h1431, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1423, h1430, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h1423, h1429, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1426, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1461 | h1461
          · rcases p0_3 (m.d 0 5) (by simp) with h1462 | h1462
            · linarith only [h1462, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1464 | h1464
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1465 | h1465
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1466 | h1466
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1467 | h1467
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1468 | h1468
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1469 | h1469
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1470 | h1470
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1471 | h1471
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1472 | h1472
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1473 | h1473
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1474 | h1474
                                  · linarith only [h1425, h1465, h1471, h1474, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1425, h1466, h1474, hc13, hc34, hlam, hphi, p0_1]
                                · linarith only [h1425, h1466, h1471, h1473, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1425, h1466, h1471, h1472, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1424, h1471, hlam]
                          · linarith only [h1424, h1425, h1466, h1470, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1425, h1466, h1467, h1469, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1425, h1466, h1467, h1468, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1423, h1467, hlam]
                  · linarith only [h1423, h1425, h1466, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1423, h1425, h1465, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1423, h1464, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1461, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1488 | h1488
        · rcases p0_3 (m.d 0 4) (by simp) with h1489 | h1489
          · rcases p0_3 (m.d 0 5) (by simp) with h1490 | h1490
            · linarith only [h1490, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1492 | h1492
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1493 | h1493
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1494 | h1494
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1495 | h1495
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1496 | h1496
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1497 | h1497
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1498 | h1498
                          · linarith only [h1424, h1488, h1494, h1498, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1424, h1488, h1493, h1498, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h1424, h1488, h1493, h1494, h1497, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1424, h1488, h1493, h1494, h1496, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1423, h1495, hlam]
                  · linarith only [h1423, h1424, h1493, h1494, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1423, h1424, h1493, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1423, h1492, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1489, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1508 | h1508
          · rcases p0_3 (m.d 0 5) (by simp) with h1509 | h1509
            · linarith only [h1509, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1511 | h1511
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1512 | h1512
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1513 | h1513
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1514 | h1514
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1515 | h1515
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1516 | h1516
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1517 | h1517
                          · linarith only [h1424, h1514, h1517, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1519 | h1519
                            · linarith only [h1488, h1514, h1517, h1519, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1488, h1517, h1519, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h1424, h1512, h1514, h1516, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1424, h1512, h1514, h1515, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1423, h1514, hlam]
                  · linarith only [h1423, h1424, h1512, h1513, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1423, h1424, h1512, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1423, h1511, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1508, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1529 | h1529
      · rcases p0_3 (m.d 0 3) (by simp) with h1530 | h1530
        · rcases p0_3 (m.d 0 4) (by simp) with h1531 | h1531
          · rcases p0_3 (m.d 0 5) (by simp) with h1532 | h1532
            · linarith only [h1532, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1534 | h1534
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1535 | h1535
                · linarith only [h1423, h1535, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1423, h1529, h1535, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1529, h1534, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1531, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1540 | h1540
          · rcases p0_3 (m.d 0 5) (by simp) with h1541 | h1541
            · linarith only [h1541, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1543 | h1543
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1544 | h1544
                · linarith only [h1423, h1529, h1544, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1423, h1529, h1544, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1529, h1543, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1540, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1549 | h1549
        · rcases p0_3 (m.d 0 4) (by simp) with h1550 | h1550
          · rcases p0_3 (m.d 0 5) (by simp) with h1551 | h1551
            · linarith only [h1551, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1553 | h1553
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1554 | h1554
                · linarith only [h1423, h1554, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1556 | h1556
                  · linarith only [h1529, h1554, h1556, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1529, h1549, h1554, h1556, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1553, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1550, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1561 | h1561
          · rcases p0_3 (m.d 0 5) (by simp) with h1562 | h1562
            · linarith only [h1562, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1564 | h1564
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1565 | h1565
                · linarith only [h1423, h1565, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1567 | h1567
                  · linarith only [h1529, h1565, h1567, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1569 | h1569
                    · linarith only [h1529, h1565, h1569, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1529, h1565, h1569, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1564, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1561, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1575 | h1575
    · linarith only [h1575, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1577 | h1577
      · rcases p0_3 (m.d 0 3) (by simp) with h1578 | h1578
        · rcases p0_3 (m.d 0 4) (by simp) with h1579 | h1579
          · rcases p0_3 (m.d 0 5) (by simp) with h1580 | h1580
            · rcases p0_3 (m.d 0 6) (by simp) with h1581 | h1581
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1582 | h1582
                · linarith only [h1577, h1582, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1582, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1577, h1581, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1580, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1587 | h1587
            · rcases p0_3 (m.d 0 6) (by simp) with h1588 | h1588
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1589 | h1589
                · linarith only [h1577, h1589, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1589, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1577, h1588, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1587, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1594 | h1594
          · rcases p0_3 (m.d 0 5) (by simp) with h1595 | h1595
            · rcases p0_3 (m.d 0 6) (by simp) with h1596 | h1596
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1597 | h1597
                · linarith only [h1577, h1597, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1597, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1577, h1596, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1595, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1602 | h1602
            · rcases p0_3 (m.d 0 6) (by simp) with h1603 | h1603
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1604 | h1604
                · linarith only [h1577, h1604, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1604, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1577, h1603, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1602, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1609 | h1609
        · rcases p0_3 (m.d 0 4) (by simp) with h1610 | h1610
          · rcases p0_3 (m.d 0 5) (by simp) with h1611 | h1611
            · rcases p0_3 (m.d 0 6) (by simp) with h1612 | h1612
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1613 | h1613
                · linarith only [h1613, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1613, hlam]
              · linarith only [h1612, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1611, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1618 | h1618
            · rcases p0_3 (m.d 0 6) (by simp) with h1619 | h1619
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1620 | h1620
                · linarith only [h1620, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1620, hlam]
              · linarith only [h1619, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1618, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1625 | h1625
          · rcases p0_3 (m.d 0 5) (by simp) with h1626 | h1626
            · rcases p0_3 (m.d 0 6) (by simp) with h1627 | h1627
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1628 | h1628
                · linarith only [h1628, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1628, hlam]
              · linarith only [h1627, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1626, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1633 | h1633
            · rcases p0_3 (m.d 0 6) (by simp) with h1634 | h1634
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1635 | h1635
                · linarith only [h1635, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1577, h1635, hlam]
              · linarith only [h1634, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1633, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1640 | h1640
    · rcases p0_3 (m.d 0 2) (by simp) with h1641 | h1641
      · linarith only [h1641, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1643 | h1643
        · rcases p0_3 (m.d 0 4) (by simp) with h1644 | h1644
          · rcases p0_3 (m.d 0 5) (by simp) with h1645 | h1645
            · rcases p0_3 (m.d 0 6) (by simp) with h1646 | h1646
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1647 | h1647
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1648 | h1648
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1649 | h1649
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1650 | h1650
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1651 | h1651
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1652 | h1652
                          · linarith only [h1643, h1648, h1652, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1643, h1652, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1647, h1650, h1651, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1640, h1650, hlam]
                    · linarith only [h1643, h1647, h1648, h1649, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1640, h1647, h1648, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1640, h1647, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1640, h1646, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1645, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1662 | h1662
            · rcases p0_3 (m.d 0 6) (by simp) with h1663 | h1663
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1664 | h1664
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1665 | h1665
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1666 | h1666
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1667 | h1667
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1668 | h1668
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1669 | h1669
                          · linarith only [h1643, h1665, h1669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1643, h1669, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h1643, h1664, h1665, h1668, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1640, h1667, hlam]
                    · linarith only [h1643, h1664, h1665, h1666, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1640, h1664, h1665, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1640, h1664, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1640, h1663, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1662, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1679 | h1679
          · rcases p0_3 (m.d 0 5) (by simp) with h1680 | h1680
            · rcases p0_3 (m.d 0 6) (by simp) with h1681 | h1681
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1682 | h1682
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1683 | h1683
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1684 | h1684
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1685 | h1685
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1686 | h1686
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1687 | h1687
                          · linarith only [h1679, h1684, h1687, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1643, h1687, hlam]
                        · linarith only [h1679, h1684, h1686, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1640, h1685, hlam]
                    · linarith only [h1640, h1682, h1684, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1640, h1682, h1683, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1640, h1682, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1640, h1681, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1680, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1697 | h1697
            · rcases p0_3 (m.d 0 6) (by simp) with h1698 | h1698
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1699 | h1699
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1700 | h1700
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1701 | h1701
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1702 | h1702
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1703 | h1703
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1704 | h1704
                          · linarith only [h1702, h1704, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1643, h1704, hlam]
                        · linarith only [h1702, h1703, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1640, h1702, hlam]
                    · linarith only [h1640, h1699, h1701, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1640, h1699, h1700, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1640, h1699, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1640, h1698, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1697, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1714 | h1714
      · linarith only [h1714, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1716 | h1716
        · rcases p0_3 (m.d 0 4) (by simp) with h1717 | h1717
          · rcases p0_3 (m.d 0 5) (by simp) with h1718 | h1718
            · rcases p0_3 (m.d 0 6) (by simp) with h1719 | h1719
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1720 | h1720
                · linarith only [h1640, h1720, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1722 | h1722
                  · linarith only [h1720, h1722, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1716, h1720, h1722, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1719, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1718, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1727 | h1727
            · rcases p0_3 (m.d 0 6) (by simp) with h1728 | h1728
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1729 | h1729
                · linarith only [h1640, h1729, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1731 | h1731
                  · linarith only [h1729, h1731, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1716, h1729, h1731, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1728, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1727, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1736 | h1736
          · rcases p0_3 (m.d 0 5) (by simp) with h1737 | h1737
            · rcases p0_3 (m.d 0 6) (by simp) with h1738 | h1738
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1739 | h1739
                · linarith only [h1640, h1739, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1741 | h1741
                  · linarith only [h1739, h1741, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1743 | h1743
                    · linarith only [h1739, h1743, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1736, h1739, h1743, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1738, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1737, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1748 | h1748
            · rcases p0_3 (m.d 0 6) (by simp) with h1749 | h1749
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1750 | h1750
                · linarith only [h1640, h1750, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1752 | h1752
                  · linarith only [h1750, h1752, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1754 | h1754
                    · linarith only [h1750, h1754, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1756 | h1756
                      · linarith only [h1750, h1756, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h1750, h1756, hc01, hc15, hlam, hphi, p0_1]
              · linarith only [h1749, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1748, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1761 | h1761
    · rcases p0_3 (m.d 0 2) (by simp) with h1762 | h1762
      · rcases p0_3 (m.d 0 3) (by simp) with h1763 | h1763
        · linarith only [h1763, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1765 | h1765
          · rcases p0_3 (m.d 0 5) (by simp) with h1766 | h1766
            · rcases p0_3 (m.d 0 6) (by simp) with h1767 | h1767
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1768 | h1768
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1769 | h1769
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1770 | h1770
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1771 | h1771
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1772 | h1772
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1773 | h1773
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1774 | h1774
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1775 | h1775
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1776 | h1776
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1777 | h1777
                                  · linarith only [h1765, h1768, h1774, h1777, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1765, h1777, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h1765, h1769, h1774, h1776, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1762, h1775, hlam]
                            · linarith only [h1762, h1769, h1774, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1762, h1769, h1773, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1769, h1771, h1772, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1761, h1771, hlam]
                    · linarith only [h1761, h1769, h1770, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1762, h1768, h1769, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1761, h1768, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1761, h1767, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1766, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1791 | h1791
            · rcases p0_3 (m.d 0 6) (by simp) with h1792 | h1792
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1793 | h1793
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1794 | h1794
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1795 | h1795
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1796 | h1796
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1797 | h1797
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1798 | h1798
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1799 | h1799
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1800 | h1800
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1801 | h1801
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1802 | h1802
                                  · linarith only [h1793, h1800, h1802, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h1765, h1802, hlam]
                                · linarith only [h1800, h1801, hc03, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1762, h1800, hlam]
                            · linarith only [h1762, h1794, h1799, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1762, h1794, h1798, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1794, h1796, h1797, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1761, h1796, hlam]
                    · linarith only [h1761, h1794, h1795, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1762, h1793, h1794, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1761, h1793, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1761, h1792, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1791, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1816 | h1816
        · linarith only [h1816, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1818 | h1818
          · rcases p0_3 (m.d 0 5) (by simp) with h1819 | h1819
            · rcases p0_3 (m.d 0 6) (by simp) with h1820 | h1820
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1821 | h1821
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1822 | h1822
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1823 | h1823
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1824 | h1824
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1825 | h1825
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1826 | h1826
                          · linarith only [h1762, h1826, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1828 | h1828
                            · linarith only [h1818, h1823, h1826, h1828, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1818, h1821, h1826, h1828, hc12, hc24, hlam, hphi, p0_1]
                        · linarith only [h1818, h1823, h1825, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1761, h1824, hlam]
                    · linarith only [h1761, h1762, h1821, h1823, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1761, h1762, h1821, h1822, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1761, h1762, h1821, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1761, h1820, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1819, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1838 | h1838
            · rcases p0_3 (m.d 0 6) (by simp) with h1839 | h1839
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1840 | h1840
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1841 | h1841
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1842 | h1842
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1843 | h1843
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1844 | h1844
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1845 | h1845
                          · linarith only [h1762, h1845, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1847 | h1847
                            · linarith only [h1843, h1845, h1847, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1849 | h1849
                              · linarith only [h1843, h1845, h1849, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · linarith only [h1845, h1849, hc02, hc25, hlam, hphi, p0_1]
                        · linarith only [h1843, h1844, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1761, h1843, hlam]
                    · linarith only [h1761, h1762, h1840, h1842, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1761, h1762, h1840, h1841, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1761, h1762, h1840, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1761, h1839, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1838, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1859 | h1859
      · rcases p0_3 (m.d 0 3) (by simp) with h1860 | h1860
        · linarith only [h1860, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1862 | h1862
          · rcases p0_3 (m.d 0 5) (by simp) with h1863 | h1863
            · rcases p0_3 (m.d 0 6) (by simp) with h1864 | h1864
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1865 | h1865
                · linarith only [h1761, h1865, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1761, h1859, h1865, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1859, h1864, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1863, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1870 | h1870
            · rcases p0_3 (m.d 0 6) (by simp) with h1871 | h1871
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1872 | h1872
                · linarith only [h1761, h1859, h1872, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1761, h1859, h1872, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1859, h1871, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1870, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1877 | h1877
        · linarith only [h1877, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1879 | h1879
          · rcases p0_3 (m.d 0 5) (by simp) with h1880 | h1880
            · rcases p0_3 (m.d 0 6) (by simp) with h1881 | h1881
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1882 | h1882
                · linarith only [h1761, h1882, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1884 | h1884
                  · linarith only [h1761, h1884, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1886 | h1886
                    · linarith only [h1859, h1882, h1886, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1859, h1879, h1882, h1886, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1881, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1880, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1891 | h1891
            · rcases p0_3 (m.d 0 6) (by simp) with h1892 | h1892
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1893 | h1893
                · linarith only [h1761, h1893, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1895 | h1895
                  · linarith only [h1761, h1895, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1897 | h1897
                    · linarith only [h1859, h1893, h1897, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1899 | h1899
                      · linarith only [h1859, h1893, h1899, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h1859, h1893, h1899, hc01, hc15, hlam, hphi, p0_1]
              · linarith only [h1892, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1891, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1904 | h1904
    · rcases p0_3 (m.d 0 2) (by simp) with h1905 | h1905
      · rcases p0_3 (m.d 0 3) (by simp) with h1906 | h1906
        · rcases p0_3 (m.d 0 4) (by simp) with h1907 | h1907
          · linarith only [h1907, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1909 | h1909
            · rcases p0_3 (m.d 0 6) (by simp) with h1910 | h1910
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1911 | h1911
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1912 | h1912
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1913 | h1913
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1914 | h1914
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1915 | h1915
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1916 | h1916
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1917 | h1917
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1918 | h1918
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1919 | h1919
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1920 | h1920
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1921 | h1921
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h1922 | h1922
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h1923 | h1923
                                        · linarith only [h1923, hlam, p0_0]
                                        · linarith only [h1913, h1923, hc14, hc45, hlam, hphi, p0_1]
                                      · linarith only [h1913, h1921, h1922, hc14, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                    · linarith only [h1906, h1921, hlam]
                                  · linarith only [h1906, h1913, h1920, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h1913, h1918, h1919, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1905, h1918, hlam]
                            · linarith only [h1905, h1913, h1917, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1905, h1913, h1916, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1913, h1914, h1915, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1904, h1914, hlam]
                    · linarith only [h1904, h1913, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1905, h1911, h1912, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1904, h1911, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1904, h1910, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1909, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1940 | h1940
          · linarith only [h1940, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1942 | h1942
            · rcases p0_3 (m.d 0 6) (by simp) with h1943 | h1943
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1944 | h1944
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1945 | h1945
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1946 | h1946
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1947 | h1947
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1948 | h1948
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1949 | h1949
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h1950 | h1950
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h1951 | h1951
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h1952 | h1952
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h1953 | h1953
                                  · linarith only [h1906, h1953, hlam]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h1955 | h1955
                                    · linarith only [h1944, h1951, h1953, h1955, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · linarith only [h1945, h1953, h1955, hc13, hc35, hlam, hphi, p0_1]
                                · linarith only [h1951, h1952, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1905, h1951, hlam]
                            · linarith only [h1905, h1906, h1945, h1950, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1905, h1906, h1945, h1949, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1906, h1945, h1947, h1948, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1904, h1947, hlam]
                    · linarith only [h1904, h1906, h1945, h1946, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1905, h1906, h1944, h1945, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1904, h1906, h1944, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1904, h1943, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1942, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1969 | h1969
        · rcases p0_3 (m.d 0 4) (by simp) with h1970 | h1970
          · linarith only [h1970, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1972 | h1972
            · rcases p0_3 (m.d 0 6) (by simp) with h1973 | h1973
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1974 | h1974
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1975 | h1975
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1976 | h1976
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1977 | h1977
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1978 | h1978
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1979 | h1979
                          · linarith only [h1905, h1969, h1975, h1979, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1905, h1969, h1974, h1979, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h1905, h1969, h1974, h1975, h1978, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1904, h1977, hlam]
                    · linarith only [h1905, h1969, h1974, h1975, h1976, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1904, h1905, h1974, h1975, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1904, h1905, h1974, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1904, h1973, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1972, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1989 | h1989
          · linarith only [h1989, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1991 | h1991
            · rcases p0_3 (m.d 0 6) (by simp) with h1992 | h1992
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1993 | h1993
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1994 | h1994
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1995 | h1995
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1996 | h1996
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1997 | h1997
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h1998 | h1998
                          · linarith only [h1905, h1996, h1998, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2000 | h2000
                            · linarith only [h1905, h2000, hlam]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2002 | h2002
                              · linarith only [h1969, h1996, h1998, h2002, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · linarith only [h1969, h1998, h2002, hc02, hc25, hlam, hphi, p0_1]
                        · linarith only [h1905, h1993, h1996, h1997, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1904, h1996, hlam]
                    · linarith only [h1904, h1905, h1993, h1995, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1904, h1905, h1993, h1994, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1904, h1905, h1993, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1904, h1992, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1991, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2012 | h2012
      · rcases p0_3 (m.d 0 3) (by simp) with h2013 | h2013
        · rcases p0_3 (m.d 0 4) (by simp) with h2014 | h2014
          · linarith only [h2014, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2016 | h2016
            · rcases p0_3 (m.d 0 6) (by simp) with h2017 | h2017
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2018 | h2018
                · linarith only [h1904, h2018, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1904, h2012, h2018, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2012, h2017, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h2016, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2023 | h2023
          · linarith only [h2023, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2025 | h2025
            · rcases p0_3 (m.d 0 6) (by simp) with h2026 | h2026
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2027 | h2027
                · linarith only [h1904, h2012, h2027, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1904, h2012, h2027, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2012, h2026, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h2025, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2032 | h2032
        · rcases p0_3 (m.d 0 4) (by simp) with h2033 | h2033
          · linarith only [h2033, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2035 | h2035
            · rcases p0_3 (m.d 0 6) (by simp) with h2036 | h2036
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2037 | h2037
                · linarith only [h1904, h2037, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2039 | h2039
                  · linarith only [h2012, h2037, h2039, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2012, h2032, h2037, h2039, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2036, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h2035, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2044 | h2044
          · linarith only [h2044, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2046 | h2046
            · rcases p0_3 (m.d 0 6) (by simp) with h2047 | h2047
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2048 | h2048
                · linarith only [h1904, h2048, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2050 | h2050
                  · linarith only [h2012, h2048, h2050, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2052 | h2052
                    · linarith only [h1904, h2052, hlam]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2054 | h2054
                      · linarith only [h2012, h2048, h2054, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2012, h2048, h2054, hc01, hc15, hlam, hphi, p0_1]
              · linarith only [h2047, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h2046, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2061 | h2061
    · linarith only [h2061, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2063 | h2063
      · rcases p0_3 (m.d 0 3) (by simp) with h2064 | h2064
        · rcases p0_3 (m.d 0 4) (by simp) with h2065 | h2065
          · rcases p0_3 (m.d 0 5) (by simp) with h2066 | h2066
            · rcases p0_3 (m.d 0 6) (by simp) with h2067 | h2067
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2068 | h2068
                · linarith only [h2063, h2068, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2068, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2067, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2072 | h2072
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2073 | h2073
                · linarith only [h2063, h2073, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2073, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2072, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2077 | h2077
            · rcases p0_3 (m.d 0 6) (by simp) with h2078 | h2078
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2079 | h2079
                · linarith only [h2063, h2079, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2079, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2078, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2083 | h2083
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2084 | h2084
                · linarith only [h2063, h2084, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2084, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2083, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2088 | h2088
          · rcases p0_3 (m.d 0 5) (by simp) with h2089 | h2089
            · rcases p0_3 (m.d 0 6) (by simp) with h2090 | h2090
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2091 | h2091
                · linarith only [h2063, h2091, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2091, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2090, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2095 | h2095
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2096 | h2096
                · linarith only [h2063, h2096, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2096, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2095, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2100 | h2100
            · rcases p0_3 (m.d 0 6) (by simp) with h2101 | h2101
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2102 | h2102
                · linarith only [h2063, h2102, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2102, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2101, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2106 | h2106
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2107 | h2107
                · linarith only [h2063, h2107, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2107, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2106, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2111 | h2111
        · rcases p0_3 (m.d 0 4) (by simp) with h2112 | h2112
          · rcases p0_3 (m.d 0 5) (by simp) with h2113 | h2113
            · rcases p0_3 (m.d 0 6) (by simp) with h2114 | h2114
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2115 | h2115
                · linarith only [h2111, h2115, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2115, hlam]
              · linarith only [h2114, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2119 | h2119
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2120 | h2120
                · linarith only [h2111, h2120, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2120, hlam]
              · linarith only [h2119, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2124 | h2124
            · rcases p0_3 (m.d 0 6) (by simp) with h2125 | h2125
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2126 | h2126
                · linarith only [h2111, h2126, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2126, hlam]
              · linarith only [h2125, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2130 | h2130
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2131 | h2131
                · linarith only [h2111, h2131, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2131, hlam]
              · linarith only [h2130, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2135 | h2135
          · rcases p0_3 (m.d 0 5) (by simp) with h2136 | h2136
            · rcases p0_3 (m.d 0 6) (by simp) with h2137 | h2137
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2138 | h2138
                · linarith only [h2135, h2138, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2138, hlam]
              · linarith only [h2137, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2142 | h2142
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2143 | h2143
                · linarith only [h2135, h2143, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2143, hlam]
              · linarith only [h2142, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2147 | h2147
            · rcases p0_3 (m.d 0 6) (by simp) with h2148 | h2148
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2149 | h2149
                · linarith only [h2147, h2149, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2149, hlam]
              · linarith only [h2148, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2153 | h2153
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2154 | h2154
                · linarith only [h2154, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2063, h2154, hlam]
              · linarith only [h2153, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2158 | h2158
    · rcases p0_3 (m.d 0 2) (by simp) with h2159 | h2159
      · linarith only [h2159, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2161 | h2161
        · rcases p0_3 (m.d 0 4) (by simp) with h2162 | h2162
          · rcases p0_3 (m.d 0 5) (by simp) with h2163 | h2163
            · rcases p0_3 (m.d 0 6) (by simp) with h2164 | h2164
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2165 | h2165
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2166 | h2166
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2167 | h2167
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2168 | h2168
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2169 | h2169
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2170 | h2170
                          · linarith only [h2161, h2166, h2170, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2170, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2158, h2169, hlam]
                      · linarith only [h2158, h2165, h2168, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2161, h2165, h2166, h2167, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2165, h2166, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2165, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2164, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2179 | h2179
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2180 | h2180
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2181 | h2181
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2182 | h2182
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2183 | h2183
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2184 | h2184
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2185 | h2185
                          · linarith only [h2161, h2181, h2185, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2185, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2158, h2184, hlam]
                      · linarith only [h2161, h2180, h2181, h2183, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2161, h2180, h2181, h2182, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2180, h2181, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2180, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2179, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2194 | h2194
            · rcases p0_3 (m.d 0 6) (by simp) with h2195 | h2195
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2196 | h2196
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2197 | h2197
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2198 | h2198
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2199 | h2199
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2200 | h2200
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2201 | h2201
                          · linarith only [h2161, h2197, h2201, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2201, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2158, h2200, hlam]
                      · linarith only [h2161, h2196, h2197, h2199, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2161, h2196, h2197, h2198, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2196, h2197, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2196, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2195, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2210 | h2210
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2211 | h2211
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2212 | h2212
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2213 | h2213
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2214 | h2214
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2215 | h2215
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2216 | h2216
                          · linarith only [h2161, h2212, h2216, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2216, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2158, h2215, hlam]
                      · linarith only [h2161, h2211, h2212, h2214, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2161, h2211, h2212, h2213, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2211, h2212, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2211, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2210, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2225 | h2225
          · rcases p0_3 (m.d 0 5) (by simp) with h2226 | h2226
            · rcases p0_3 (m.d 0 6) (by simp) with h2227 | h2227
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2228 | h2228
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2229 | h2229
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2230 | h2230
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2231 | h2231
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2232 | h2232
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2233 | h2233
                          · linarith only [h2225, h2230, h2233, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2233, hlam]
                        · linarith only [h2158, h2232, hlam]
                      · linarith only [h2225, h2230, h2231, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2158, h2228, h2230, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2228, h2229, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2228, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2227, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2242 | h2242
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2243 | h2243
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2244 | h2244
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2245 | h2245
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2246 | h2246
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2247 | h2247
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2248 | h2248
                          · linarith only [h2225, h2245, h2248, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2248, hlam]
                        · linarith only [h2158, h2247, hlam]
                      · linarith only [h2225, h2245, h2246, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2158, h2243, h2245, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2243, h2244, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2243, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2242, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2257 | h2257
            · rcases p0_3 (m.d 0 6) (by simp) with h2258 | h2258
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2259 | h2259
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2260 | h2260
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2261 | h2261
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2262 | h2262
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2263 | h2263
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2264 | h2264
                          · linarith only [h2257, h2262, h2264, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2264, hlam]
                        · linarith only [h2158, h2263, hlam]
                      · linarith only [h2158, h2262, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2158, h2259, h2261, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2259, h2260, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2259, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2258, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2273 | h2273
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2274 | h2274
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2275 | h2275
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2276 | h2276
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2277 | h2277
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2278 | h2278
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2279 | h2279
                          · linarith only [h2278, h2279, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2161, h2279, hlam]
                        · linarith only [h2158, h2278, hlam]
                      · linarith only [h2158, h2277, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2158, h2274, h2276, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2158, h2274, h2275, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2158, h2274, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2273, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2288 | h2288
      · linarith only [h2288, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2290 | h2290
        · rcases p0_3 (m.d 0 4) (by simp) with h2291 | h2291
          · rcases p0_3 (m.d 0 5) (by simp) with h2292 | h2292
            · rcases p0_3 (m.d 0 6) (by simp) with h2293 | h2293
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2294 | h2294
                · linarith only [h2158, h2294, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2296 | h2296
                  · linarith only [h2290, h2294, h2296, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2290, h2294, h2296, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2293, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2300 | h2300
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2301 | h2301
                · linarith only [h2158, h2301, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2303 | h2303
                  · linarith only [h2290, h2301, h2303, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2290, h2301, h2303, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2300, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2307 | h2307
            · rcases p0_3 (m.d 0 6) (by simp) with h2308 | h2308
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2309 | h2309
                · linarith only [h2158, h2309, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2311 | h2311
                  · linarith only [h2290, h2309, h2311, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2290, h2309, h2311, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2308, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2315 | h2315
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2316 | h2316
                · linarith only [h2158, h2316, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2318 | h2318
                  · linarith only [h2290, h2316, h2318, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2290, h2316, h2318, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2315, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2322 | h2322
          · rcases p0_3 (m.d 0 5) (by simp) with h2323 | h2323
            · rcases p0_3 (m.d 0 6) (by simp) with h2324 | h2324
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2325 | h2325
                · linarith only [h2158, h2325, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2327 | h2327
                  · linarith only [h2322, h2325, h2327, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2329 | h2329
                    · linarith only [h2322, h2325, h2329, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2322, h2325, h2329, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2324, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2333 | h2333
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2334 | h2334
                · linarith only [h2158, h2334, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2336 | h2336
                  · linarith only [h2322, h2334, h2336, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2338 | h2338
                    · linarith only [h2322, h2334, h2338, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2322, h2334, h2338, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2333, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2342 | h2342
            · rcases p0_3 (m.d 0 6) (by simp) with h2343 | h2343
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2344 | h2344
                · linarith only [h2158, h2344, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2346 | h2346
                  · linarith only [h2342, h2344, h2346, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2348 | h2348
                    · linarith only [h2342, h2344, h2348, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2350 | h2350
                      · linarith only [h2342, h2344, h2350, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2342, h2344, h2350, hc01, hc15, hlam, hphi, p0_1]
              · linarith only [h2343, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2354 | h2354
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2355 | h2355
                · linarith only [h2158, h2355, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2357 | h2357
                  · linarith only [h2355, h2357, hc06, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2359 | h2359
                    · linarith only [h2355, h2359, hc06, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2361 | h2361
                      · linarith only [h2355, h2361, hc06, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2363 | h2363
                        · linarith only [h2355, h2363, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                        · linarith only [h2355, h2363, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2354, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2367 | h2367
    · rcases p0_3 (m.d 0 2) (by simp) with h2368 | h2368
      · rcases p0_3 (m.d 0 3) (by simp) with h2369 | h2369
        · linarith only [h2369, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2371 | h2371
          · rcases p0_3 (m.d 0 5) (by simp) with h2372 | h2372
            · rcases p0_3 (m.d 0 6) (by simp) with h2373 | h2373
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2374 | h2374
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2375 | h2375
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2376 | h2376
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2377 | h2377
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2378 | h2378
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2379 | h2379
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2380 | h2380
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2381 | h2381
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2382 | h2382
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2383 | h2383
                                  · linarith only [h2371, h2374, h2380, h2383, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2371, h2383, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2368, h2382, hlam]
                              · linarith only [h2371, h2375, h2380, h2381, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2368, h2375, h2380, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2368, h2375, h2379, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2367, h2378, hlam]
                      · linarith only [h2367, h2375, h2377, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2368, h2374, h2375, h2376, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2368, h2374, h2375, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2374, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2373, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2396 | h2396
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2397 | h2397
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2398 | h2398
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2399 | h2399
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2400 | h2400
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2401 | h2401
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2402 | h2402
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2403 | h2403
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2404 | h2404
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2405 | h2405
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2406 | h2406
                                  · linarith only [h2371, h2397, h2403, h2406, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2371, h2406, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2368, h2405, hlam]
                              · linarith only [h2371, h2402, h2403, h2404, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2368, h2402, h2403, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2368, h2402, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2367, h2401, hlam]
                      · linarith only [h2367, h2398, h2400, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2368, h2397, h2398, h2399, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2368, h2397, h2398, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2397, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2396, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2419 | h2419
            · rcases p0_3 (m.d 0 6) (by simp) with h2420 | h2420
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2421 | h2421
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2422 | h2422
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2423 | h2423
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2424 | h2424
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2425 | h2425
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2426 | h2426
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2427 | h2427
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2428 | h2428
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2429 | h2429
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2430 | h2430
                                  · linarith only [h2419, h2421, h2428, h2430, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2371, h2430, hlam]
                                · linarith only [h2368, h2429, hlam]
                              · linarith only [h2368, h2426, h2428, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2368, h2426, h2427, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2368, h2426, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2367, h2425, hlam]
                      · linarith only [h2367, h2422, h2424, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2368, h2421, h2422, h2423, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2368, h2421, h2422, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2421, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2420, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2443 | h2443
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2444 | h2444
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2445 | h2445
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2446 | h2446
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2447 | h2447
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2448 | h2448
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2449 | h2449
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2450 | h2450
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2451 | h2451
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2452 | h2452
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2453 | h2453
                                  · linarith only [h2444, h2452, h2453, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2371, h2453, hlam]
                                · linarith only [h2368, h2452, hlam]
                              · linarith only [h2368, h2451, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2368, h2449, h2450, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2368, h2449, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2367, h2448, hlam]
                      · linarith only [h2367, h2445, h2447, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2368, h2444, h2445, h2446, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2368, h2444, h2445, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2444, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2443, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2466 | h2466
        · linarith only [h2466, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2468 | h2468
          · rcases p0_3 (m.d 0 5) (by simp) with h2469 | h2469
            · rcases p0_3 (m.d 0 6) (by simp) with h2470 | h2470
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2471 | h2471
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2472 | h2472
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2473 | h2473
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2474 | h2474
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2475 | h2475
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2476 | h2476
                          · linarith only [h2368, h2476, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2478 | h2478
                            · linarith only [h2468, h2473, h2476, h2478, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2468, h2471, h2476, h2478, hc12, hc24, hlam, hphi, p0_1]
                        · linarith only [h2367, h2475, hlam]
                      · linarith only [h2468, h2473, h2474, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2367, h2368, h2471, h2473, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2367, h2368, h2471, h2472, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2368, h2471, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2470, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2487 | h2487
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2488 | h2488
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2489 | h2489
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2490 | h2490
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2491 | h2491
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2492 | h2492
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2493 | h2493
                          · linarith only [h2368, h2493, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2495 | h2495
                            · linarith only [h2468, h2490, h2493, h2495, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2468, h2493, h2495, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h2367, h2492, hlam]
                      · linarith only [h2368, h2468, h2488, h2490, h2491, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2367, h2368, h2488, h2490, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2367, h2368, h2488, h2489, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2368, h2488, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2487, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2504 | h2504
            · rcases p0_3 (m.d 0 6) (by simp) with h2505 | h2505
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2506 | h2506
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2507 | h2507
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2508 | h2508
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2509 | h2509
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2510 | h2510
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2511 | h2511
                          · linarith only [h2368, h2511, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2513 | h2513
                            · linarith only [h2504, h2509, h2511, h2513, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2515 | h2515
                              · linarith only [h2504, h2509, h2511, h2515, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · linarith only [h2504, h2511, h2515, hc02, hc25, hlam, hphi, p0_1]
                        · linarith only [h2367, h2510, hlam]
                      · linarith only [h2367, h2368, h2506, h2509, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2367, h2368, h2506, h2508, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2367, h2368, h2506, h2507, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2368, h2506, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2505, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2524 | h2524
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2525 | h2525
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2526 | h2526
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2527 | h2527
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2528 | h2528
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2529 | h2529
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2530 | h2530
                          · linarith only [h2368, h2530, hlam]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2532 | h2532
                            · linarith only [h2529, h2530, h2532, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2534 | h2534
                              · linarith only [h2529, h2530, h2534, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2536 | h2536
                                · linarith only [h2529, h2530, h2536, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                                · linarith only [h2530, h2536, hc02, hc26, hlam, hphi, p0_1]
                        · linarith only [h2367, h2529, hlam]
                      · linarith only [h2367, h2368, h2525, h2528, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2367, h2368, h2525, h2527, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2367, h2368, h2525, h2526, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2368, h2525, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2524, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2545 | h2545
      · rcases p0_3 (m.d 0 3) (by simp) with h2546 | h2546
        · linarith only [h2546, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2548 | h2548
          · rcases p0_3 (m.d 0 5) (by simp) with h2549 | h2549
            · rcases p0_3 (m.d 0 6) (by simp) with h2550 | h2550
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2551 | h2551
                · linarith only [h2367, h2545, h2551, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2545, h2551, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2550, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2555 | h2555
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2556 | h2556
                · linarith only [h2367, h2545, h2556, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2545, h2556, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2555, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2560 | h2560
            · rcases p0_3 (m.d 0 6) (by simp) with h2561 | h2561
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2562 | h2562
                · linarith only [h2367, h2545, h2562, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2545, h2562, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2561, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2566 | h2566
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2567 | h2567
                · linarith only [h2367, h2545, h2567, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2367, h2545, h2567, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2566, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2571 | h2571
        · linarith only [h2571, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2573 | h2573
          · rcases p0_3 (m.d 0 5) (by simp) with h2574 | h2574
            · rcases p0_3 (m.d 0 6) (by simp) with h2575 | h2575
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2576 | h2576
                · linarith only [h2367, h2573, h2576, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2578 | h2578
                  · linarith only [h2367, h2578, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2580 | h2580
                    · linarith only [h2545, h2573, h2576, h2580, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2545, h2573, h2576, h2580, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2575, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2584 | h2584
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2585 | h2585
                · linarith only [h2367, h2573, h2585, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2587 | h2587
                  · linarith only [h2367, h2587, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2589 | h2589
                    · linarith only [h2545, h2573, h2585, h2589, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2545, h2573, h2585, h2589, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2584, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2593 | h2593
            · rcases p0_3 (m.d 0 6) (by simp) with h2594 | h2594
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2595 | h2595
                · linarith only [h2367, h2593, h2595, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2597 | h2597
                  · linarith only [h2367, h2597, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2599 | h2599
                    · linarith only [h2545, h2593, h2595, h2599, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2601 | h2601
                      · linarith only [h2545, h2593, h2595, h2601, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2545, h2593, h2595, h2601, hc01, hc15, hlam, hphi, p0_1]
              · linarith only [h2594, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2605 | h2605
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2606 | h2606
                · linarith only [h2367, h2606, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2608 | h2608
                  · linarith only [h2367, h2608, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2610 | h2610
                    · linarith only [h2545, h2606, h2610, hc06, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2612 | h2612
                      · linarith only [h2545, h2606, h2612, hc06, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2614 | h2614
                        · linarith only [h2545, h2606, h2614, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                        · linarith only [h2545, h2606, h2614, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2605, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2618 | h2618
    · rcases p0_3 (m.d 0 2) (by simp) with h2619 | h2619
      · rcases p0_3 (m.d 0 3) (by simp) with h2620 | h2620
        · rcases p0_3 (m.d 0 4) (by simp) with h2621 | h2621
          · linarith only [h2621, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2623 | h2623
            · rcases p0_3 (m.d 0 6) (by simp) with h2624 | h2624
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2625 | h2625
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2626 | h2626
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2627 | h2627
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2628 | h2628
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2629 | h2629
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2630 | h2630
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2631 | h2631
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2632 | h2632
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2633 | h2633
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2634 | h2634
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2635 | h2635
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2636 | h2636
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2637 | h2637
                                        · linarith only [h2623, h2625, h2630, h2635, h2637, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · linarith only [h2623, h2637, hc04, hc45, hlam, hphi, p0_1]
                                      · linarith only [h2620, h2636, hlam]
                                    · linarith only [h2620, h2627, h2635, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2620, h2627, h2634, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h2619, h2633, hlam]
                              · linarith only [h2619, h2627, h2632, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2620, h2627, h2630, h2631, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2619, h2627, h2630, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2618, h2629, hlam]
                      · linarith only [h2618, h2627, h2628, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2619, h2625, h2627, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2619, h2625, h2626, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2625, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h2624, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2653 | h2653
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2654 | h2654
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2655 | h2655
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2656 | h2656
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2657 | h2657
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2658 | h2658
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2659 | h2659
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2660 | h2660
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2661 | h2661
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2662 | h2662
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2663 | h2663
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2664 | h2664
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2665 | h2665
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2666 | h2666
                                        · linarith only [h2654, h2659, h2665, h2666, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                        · linarith only [h2623, h2666, hlam]
                                      · linarith only [h2620, h2665, hlam]
                                    · linarith only [h2620, h2656, h2664, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2620, h2656, h2663, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h2619, h2662, hlam]
                              · linarith only [h2619, h2656, h2661, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2620, h2656, h2659, h2660, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2619, h2656, h2659, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2618, h2658, hlam]
                      · linarith only [h2618, h2656, h2657, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2619, h2654, h2656, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2619, h2654, h2655, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2654, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h2653, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2682 | h2682
          · linarith only [h2682, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2684 | h2684
            · rcases p0_3 (m.d 0 6) (by simp) with h2685 | h2685
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2686 | h2686
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2687 | h2687
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2688 | h2688
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2689 | h2689
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2690 | h2690
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2691 | h2691
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2692 | h2692
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2693 | h2693
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2694 | h2694
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2695 | h2695
                                  · linarith only [h2620, h2695, hlam]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2697 | h2697
                                    · linarith only [h2684, h2686, h2693, h2695, h2697, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · linarith only [h2684, h2695, h2697, hc03, hc35, hlam, hphi, p0_1]
                                · linarith only [h2619, h2694, hlam]
                              · linarith only [h2619, h2693, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2619, h2620, h2687, h2692, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2619, h2620, h2687, h2691, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2618, h2690, hlam]
                      · linarith only [h2618, h2620, h2687, h2689, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2619, h2620, h2686, h2687, h2688, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2619, h2620, h2686, h2687, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2620, h2686, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2685, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2710 | h2710
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2711 | h2711
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2712 | h2712
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2713 | h2713
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2714 | h2714
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2715 | h2715
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2716 | h2716
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2717 | h2717
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2718 | h2718
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2719 | h2719
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2720 | h2720
                                  · linarith only [h2620, h2720, hlam]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2722 | h2722
                                    · linarith only [h2711, h2719, h2720, h2722, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2724 | h2724
                                      · linarith only [h2711, h2719, h2720, h2724, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi3]
                                      · linarith only [h2720, h2724, hc03, hc36, hlam, hphi, p0_1]
                                · linarith only [h2619, h2719, hlam]
                              · linarith only [h2619, h2718, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2619, h2620, h2712, h2717, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2619, h2620, h2712, h2716, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2618, h2715, hlam]
                      · linarith only [h2618, h2620, h2712, h2714, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2619, h2620, h2711, h2712, h2713, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2619, h2620, h2711, h2712, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2620, h2711, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2710, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2737 | h2737
        · rcases p0_3 (m.d 0 4) (by simp) with h2738 | h2738
          · linarith only [h2738, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2740 | h2740
            · rcases p0_3 (m.d 0 6) (by simp) with h2741 | h2741
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2742 | h2742
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2743 | h2743
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2744 | h2744
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2745 | h2745
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2746 | h2746
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2747 | h2747
                          · linarith only [h2619, h2737, h2743, h2747, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2619, h2737, h2742, h2747, hc12, hc23, hlam, hphi, p0_1]
                        · linarith only [h2618, h2746, hlam]
                      · linarith only [h2619, h2737, h2742, h2743, h2745, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2619, h2737, h2742, h2743, h2744, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2618, h2619, h2742, h2743, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2619, h2742, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2741, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2756 | h2756
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2757 | h2757
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2758 | h2758
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2759 | h2759
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2760 | h2760
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2761 | h2761
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2762 | h2762
                          · linarith only [h2619, h2737, h2758, h2762, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2619, h2737, h2762, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2618, h2761, hlam]
                      · linarith only [h2619, h2737, h2757, h2758, h2760, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2619, h2737, h2757, h2758, h2759, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2618, h2619, h2757, h2758, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2619, h2757, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2756, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2771 | h2771
          · linarith only [h2771, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2773 | h2773
            · rcases p0_3 (m.d 0 6) (by simp) with h2774 | h2774
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2775 | h2775
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2776 | h2776
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2777 | h2777
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2778 | h2778
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2779 | h2779
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2780 | h2780
                          · linarith only [h2619, h2773, h2778, h2780, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2782 | h2782
                            · linarith only [h2619, h2782, hlam]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2784 | h2784
                              · linarith only [h2737, h2773, h2778, h2780, h2784, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · linarith only [h2737, h2773, h2780, h2784, hc02, hc25, hlam, hphi, p0_1]
                        · linarith only [h2618, h2779, hlam]
                      · linarith only [h2618, h2619, h2775, h2778, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2618, h2619, h2775, h2777, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2618, h2619, h2775, h2776, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2619, h2775, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2774, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2793 | h2793
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2794 | h2794
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2795 | h2795
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2796 | h2796
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2797 | h2797
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2798 | h2798
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2799 | h2799
                          · linarith only [h2619, h2798, h2799, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2801 | h2801
                            · linarith only [h2619, h2801, hlam]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2803 | h2803
                              · linarith only [h2737, h2798, h2799, h2803, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2805 | h2805
                                · linarith only [h2737, h2798, h2799, h2805, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                                · linarith only [h2737, h2799, h2805, hc02, hc26, hlam, hphi, p0_1]
                        · linarith only [h2618, h2798, hlam]
                      · linarith only [h2618, h2737, h2797, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2618, h2619, h2794, h2796, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2618, h2619, h2794, h2795, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2619, h2794, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2793, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2814 | h2814
      · rcases p0_3 (m.d 0 3) (by simp) with h2815 | h2815
        · rcases p0_3 (m.d 0 4) (by simp) with h2816 | h2816
          · linarith only [h2816, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2818 | h2818
            · rcases p0_3 (m.d 0 6) (by simp) with h2819 | h2819
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2820 | h2820
                · linarith only [h2618, h2814, h2820, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2814, h2820, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2819, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2824 | h2824
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2825 | h2825
                · linarith only [h2618, h2814, h2825, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2814, h2825, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2824, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2829 | h2829
          · linarith only [h2829, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2831 | h2831
            · rcases p0_3 (m.d 0 6) (by simp) with h2832 | h2832
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2833 | h2833
                · linarith only [h2618, h2814, h2833, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2814, h2833, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2832, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2837 | h2837
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2838 | h2838
                · linarith only [h2618, h2814, h2838, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2618, h2814, h2838, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2837, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2842 | h2842
        · rcases p0_3 (m.d 0 4) (by simp) with h2843 | h2843
          · linarith only [h2843, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2845 | h2845
            · rcases p0_3 (m.d 0 6) (by simp) with h2846 | h2846
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2847 | h2847
                · linarith only [h2618, h2842, h2847, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2849 | h2849
                  · linarith only [h2814, h2842, h2847, h2849, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2814, h2842, h2847, h2849, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2846, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2853 | h2853
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2854 | h2854
                · linarith only [h2618, h2842, h2854, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2856 | h2856
                  · linarith only [h2814, h2842, h2854, h2856, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2814, h2842, h2854, h2856, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2853, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2860 | h2860
          · linarith only [h2860, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2862 | h2862
            · rcases p0_3 (m.d 0 6) (by simp) with h2863 | h2863
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2864 | h2864
                · linarith only [h2618, h2862, h2864, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2866 | h2866
                  · linarith only [h2814, h2862, h2864, h2866, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2868 | h2868
                    · linarith only [h2618, h2868, hlam]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2870 | h2870
                      · linarith only [h2814, h2862, h2864, h2870, hc05, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · linarith only [h2814, h2862, h2864, h2870, hc01, hc15, hlam, hphi, p0_1]
              · linarith only [h2863, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2874 | h2874
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2875 | h2875
                · linarith only [h2618, h2875, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2877 | h2877
                  · linarith only [h2814, h2875, h2877, hc06, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2879 | h2879
                    · linarith only [h2618, h2879, hlam]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2881 | h2881
                      · linarith only [h2814, h2875, h2881, hc06, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2883 | h2883
                        · linarith only [h2814, h2875, h2883, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                        · linarith only [h2814, h2875, h2883, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2874, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2887 | h2887
    · rcases p0_3 (m.d 0 2) (by simp) with h2888 | h2888
      · rcases p0_3 (m.d 0 3) (by simp) with h2889 | h2889
        · rcases p0_3 (m.d 0 4) (by simp) with h2890 | h2890
          · rcases p0_3 (m.d 0 5) (by simp) with h2891 | h2891
            · linarith only [h2891, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2893 | h2893
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2894 | h2894
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2895 | h2895
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2896 | h2896
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2897 | h2897
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2898 | h2898
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2899 | h2899
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2900 | h2900
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2901 | h2901
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2902 | h2902
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2903 | h2903
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2904 | h2904
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2905 | h2905
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2906 | h2906
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2907 | h2907
                                          · rcases m.htr 0 5 6 (by decide) (by decide) with h2908 | h2908
                                            · linarith only [h2908, hlam, p0_0]
                                            · linarith only [h2897, h2908, hc15, hc56, hlam, hphi, p0_1]
                                          · linarith only [h2890, h2907, hlam]
                                        · linarith only [h2890, h2897, h2906, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, p0_1]
                                      · linarith only [h2889, h2905, hlam]
                                    · linarith only [h2890, h2897, h2903, h2904, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                  · linarith only [h2889, h2897, h2903, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                · linarith only [h2888, h2902, hlam]
                              · linarith only [h2888, h2897, h2901, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                            · linarith only [h2889, h2897, h2899, h2900, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                          · linarith only [h2888, h2897, h2899, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h2887, h2898, hlam]
                      · linarith only [h2887, h2897, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h2888, h2894, h2896, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h2888, h2894, h2895, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h2887, h2894, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h2893, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2926 | h2926
            · linarith only [h2926, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2928 | h2928
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2929 | h2929
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2930 | h2930
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2931 | h2931
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2932 | h2932
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2933 | h2933
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2934 | h2934
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2935 | h2935
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2936 | h2936
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2937 | h2937
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2938 | h2938
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2939 | h2939
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h2940 | h2940
                                      · rcases m.htr 0 4 5 (by decide) (by decide) with h2941 | h2941
                                        · linarith only [h2890, h2941, hlam]
                                        · rcases m.htr 0 4 6 (by decide) (by decide) with h2943 | h2943
                                          · linarith only [h2929, h2934, h2940, h2941, h2943, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi4]
                                          · linarith only [h2941, h2943, hc04, hc46, hlam, hphi, p0_1]
                                      · linarith only [h2889, h2940, hlam]
                                    · linarith only [h2889, h2932, h2939, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                                  · linarith only [h2889, h2890, h2931, h2938, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                                · linarith only [h2888, h2937, hlam]
                              · linarith only [h2888, h2890, h2931, h2936, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2889, h2890, h2931, h2934, h2935, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2888, h2890, h2931, h2934, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2887, h2933, hlam]
                      · linarith only [h2887, h2890, h2931, h2932, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2888, h2890, h2929, h2931, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2888, h2890, h2929, h2930, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h2890, h2929, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h2928, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2959 | h2959
          · rcases p0_3 (m.d 0 5) (by simp) with h2960 | h2960
            · linarith only [h2960, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2962 | h2962
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2963 | h2963
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2964 | h2964
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2965 | h2965
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2966 | h2966
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2967 | h2967
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2968 | h2968
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2969 | h2969
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2970 | h2970
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2971 | h2971
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2972 | h2972
                                  · linarith only [h2889, h2959, h2963, h2969, h2972, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · linarith only [h2889, h2959, h2972, hc03, hc34, hlam, hphi, p0_1]
                                · linarith only [h2888, h2971, hlam]
                              · linarith only [h2889, h2959, h2968, h2969, h2970, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2888, h2889, h2968, h2969, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2888, h2889, h2968, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2887, h2967, hlam]
                      · linarith only [h2887, h2889, h2964, h2966, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2888, h2889, h2963, h2964, h2965, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2888, h2889, h2963, h2964, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h2889, h2963, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2962, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2985 | h2985
            · linarith only [h2985, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2987 | h2987
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2988 | h2988
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2989 | h2989
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2990 | h2990
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h2991 | h2991
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h2992 | h2992
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h2993 | h2993
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h2994 | h2994
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h2995 | h2995
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h2996 | h2996
                                · rcases m.htr 0 3 4 (by decide) (by decide) with h2997 | h2997
                                  · linarith only [h2889, h2988, h2996, h2997, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                  · rcases m.htr 0 3 5 (by decide) (by decide) with h2999 | h2999
                                    · linarith only [h2889, h2999, hlam]
                                    · rcases m.htr 0 3 6 (by decide) (by decide) with h3001 | h3001
                                      · linarith only [h2959, h2988, h2996, h2997, h3001, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi3]
                                      · linarith only [h2959, h2997, h3001, hc03, hc36, hlam, hphi, p0_1]
                                · linarith only [h2888, h2996, hlam]
                              · linarith only [h2888, h2959, h2995, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2888, h2889, h2989, h2994, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2888, h2889, h2989, h2993, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2887, h2992, hlam]
                      · linarith only [h2887, h2889, h2989, h2991, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2888, h2889, h2988, h2989, h2990, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2888, h2889, h2988, h2989, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h2889, h2988, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2987, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h3014 | h3014
        · rcases p0_3 (m.d 0 4) (by simp) with h3015 | h3015
          · rcases p0_3 (m.d 0 5) (by simp) with h3016 | h3016
            · linarith only [h3016, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3018 | h3018
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3019 | h3019
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3020 | h3020
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3021 | h3021
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3022 | h3022
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3023 | h3023
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3024 | h3024
                          · linarith only [h2888, h3014, h3020, h3024, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2888, h3014, h3024, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2887, h3023, hlam]
                      · linarith only [h2888, h3014, h3019, h3020, h3022, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2888, h3014, h3019, h3020, h3021, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2887, h2888, h3019, h3020, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h2888, h3019, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h3018, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3033 | h3033
            · linarith only [h3033, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3035 | h3035
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3036 | h3036
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3037 | h3037
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3038 | h3038
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3039 | h3039
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3040 | h3040
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3041 | h3041
                          · linarith only [h2888, h3014, h3037, h3041, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2888, h3014, h3041, hc02, hc23, hlam, hphi, p0_1]
                        · linarith only [h2887, h3040, hlam]
                      · linarith only [h2888, h3014, h3036, h3037, h3039, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2888, h3014, h3036, h3037, h3038, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2887, h2888, h3036, h3037, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h2888, h3036, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h3035, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h3050 | h3050
          · rcases p0_3 (m.d 0 5) (by simp) with h3051 | h3051
            · linarith only [h3051, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3053 | h3053
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3054 | h3054
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3055 | h3055
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3056 | h3056
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3057 | h3057
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3058 | h3058
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3059 | h3059
                          · linarith only [h2888, h3050, h3056, h3059, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h3061 | h3061
                            · linarith only [h3014, h3050, h3056, h3059, h3061, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · linarith only [h3014, h3050, h3059, h3061, hc02, hc24, hlam, hphi, p0_1]
                        · linarith only [h2887, h3058, hlam]
                      · linarith only [h2888, h3050, h3054, h3056, h3057, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2887, h2888, h3054, h3056, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2887, h2888, h3054, h3055, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h2888, h3054, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h3053, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3070 | h3070
            · linarith only [h3070, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3072 | h3072
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3073 | h3073
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3074 | h3074
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3075 | h3075
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3076 | h3076
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3077 | h3077
                        · rcases m.htr 0 2 3 (by decide) (by decide) with h3078 | h3078
                          · linarith only [h2888, h3077, h3078, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 4 (by decide) (by decide) with h3080 | h3080
                            · linarith only [h3014, h3077, h3078, h3080, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                            · rcases m.htr 0 2 5 (by decide) (by decide) with h3082 | h3082
                              · linarith only [h2888, h3082, hlam]
                              · rcases m.htr 0 2 6 (by decide) (by decide) with h3084 | h3084
                                · linarith only [h3014, h3077, h3078, h3084, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                                · linarith only [h3014, h3078, h3084, hc02, hc26, hlam, hphi, p0_1]
                        · linarith only [h2887, h3077, hlam]
                      · linarith only [h2887, h2888, h3073, h3076, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2887, h2888, h3073, h3075, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2887, h2888, h3073, h3074, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h2888, h3073, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h3072, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h3093 | h3093
      · rcases p0_3 (m.d 0 3) (by simp) with h3094 | h3094
        · rcases p0_3 (m.d 0 4) (by simp) with h3095 | h3095
          · rcases p0_3 (m.d 0 5) (by simp) with h3096 | h3096
            · linarith only [h3096, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3098 | h3098
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3099 | h3099
                · linarith only [h2887, h3093, h3099, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h3093, h3099, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h3098, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3103 | h3103
            · linarith only [h3103, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3105 | h3105
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3106 | h3106
                · linarith only [h2887, h3093, h3106, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h3093, h3106, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h3105, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h3110 | h3110
          · rcases p0_3 (m.d 0 5) (by simp) with h3111 | h3111
            · linarith only [h3111, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3113 | h3113
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3114 | h3114
                · linarith only [h2887, h3093, h3114, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h3093, h3114, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h3113, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3118 | h3118
            · linarith only [h3118, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3120 | h3120
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3121 | h3121
                · linarith only [h2887, h3093, h3121, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2887, h3093, h3121, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h3120, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h3125 | h3125
        · rcases p0_3 (m.d 0 4) (by simp) with h3126 | h3126
          · rcases p0_3 (m.d 0 5) (by simp) with h3127 | h3127
            · linarith only [h3127, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3129 | h3129
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3130 | h3130
                · linarith only [h2887, h3125, h3130, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3132 | h3132
                  · linarith only [h3093, h3125, h3130, h3132, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h3093, h3125, h3130, h3132, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h3129, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3136 | h3136
            · linarith only [h3136, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3138 | h3138
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3139 | h3139
                · linarith only [h2887, h3125, h3139, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3141 | h3141
                  · linarith only [h3093, h3125, h3139, h3141, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h3093, h3125, h3139, h3141, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h3138, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h3145 | h3145
          · rcases p0_3 (m.d 0 5) (by simp) with h3146 | h3146
            · linarith only [h3146, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3148 | h3148
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3149 | h3149
                · linarith only [h2887, h3145, h3149, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3151 | h3151
                  · linarith only [h3093, h3145, h3149, h3151, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3153 | h3153
                    · linarith only [h3093, h3145, h3149, h3153, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h3093, h3145, h3149, h3153, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h3148, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h3157 | h3157
            · linarith only [h3157, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h3159 | h3159
              · rcases m.htr 0 1 2 (by decide) (by decide) with h3160 | h3160
                · linarith only [h2887, h3160, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h3162 | h3162
                  · linarith only [h3093, h3160, h3162, hc06, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h3164 | h3164
                    · linarith only [h3093, h3160, h3164, hc06, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h3166 | h3166
                      · linarith only [h2887, h3166, hlam]
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h3168 | h3168
                        · linarith only [h3093, h3160, h3168, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                        · linarith only [h3093, h3160, h3168, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h3159, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

set_option maxHeartbeats 5834000 in
theorem n8l_sBT8_H_I_M_IR (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0bigk := hb0.1
  have h6ehi := hb6.2.1
  have u6ehi0 := h6ehi (m.d 0 6) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 0 6) (by simp) with h8 | h8
              · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h5, hlam]
                  · linarith only [h10, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h9, hlam, p0_0]
              · linarith only [h8, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
              · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
                · rcases m.htr 0 1 3 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h5, hlam]
                  · linarith only [h17, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h16, hlam, p0_0]
              · linarith only [h15, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 0 6) (by simp) with h23 | h23
              · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                  · linarith only [h25, h5, hlam]
                  · linarith only [h25, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h24, hlam, p0_0]
              · linarith only [h23, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h30 | h30
              · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
                · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
                  · linarith only [h32, h5, hlam]
                  · linarith only [h32, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h31, hlam, p0_0]
              · linarith only [h30, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h37 | h37
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · rcases p0_3 (m.d 0 6) (by simp) with h39 | h39
              · rcases m.htr 0 1 2 (by decide) (by decide) with h40 | h40
                · rcases m.htr 0 1 3 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
                    · linarith only [h37, h42, hlam]
                    · linarith only [h42, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h40, h41, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h40, hlam, p0_0]
              · linarith only [h39, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h48 | h48
              · rcases m.htr 0 1 2 (by decide) (by decide) with h49 | h49
                · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h37, h51, hlam]
                    · linarith only [h51, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h49, h50, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h49, hlam, p0_0]
              · linarith only [h48, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h57 | h57
            · rcases p0_3 (m.d 0 6) (by simp) with h58 | h58
              · rcases m.htr 0 1 2 (by decide) (by decide) with h59 | h59
                · rcases m.htr 0 1 3 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h62 | h62
                      · linarith only [h58, h62, hlam]
                      · linarith only [h62, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h59, h61, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h59, h60, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h59, hlam, p0_0]
              · linarith only [h58, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h69 | h69
              · rcases m.htr 0 1 2 (by decide) (by decide) with h70 | h70
                · rcases m.htr 0 1 3 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h73 | h73
                      · linarith only [h69, h73, hlam]
                      · linarith only [h73, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h70, h72, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h70, h71, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h70, hlam, p0_0]
              · linarith only [h69, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h81 | h81
    · rcases p0_3 (m.d 0 2) (by simp) with h82 | h82
      · rcases p0_3 (m.d 0 3) (by simp) with h83 | h83
        · linarith only [h83, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h85 | h85
          · rcases p0_3 (m.d 0 5) (by simp) with h86 | h86
            · rcases p0_3 (m.d 0 6) (by simp) with h87 | h87
              · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
                · linarith only [h82, h88, hlam]
                · linarith only [h88, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h87, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h92 | h92
              · rcases m.htr 0 1 2 (by decide) (by decide) with h93 | h93
                · linarith only [h82, h93, hlam]
                · linarith only [h93, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h92, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h97 | h97
            · rcases p0_3 (m.d 0 6) (by simp) with h98 | h98
              · rcases m.htr 0 1 2 (by decide) (by decide) with h99 | h99
                · linarith only [h82, h99, hlam]
                · linarith only [h99, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h98, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h103 | h103
              · rcases m.htr 0 1 2 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h82, hlam]
                · linarith only [h104, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h103, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h108 | h108
        · linarith only [h108, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h110 | h110
          · rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
            · rcases p0_3 (m.d 0 6) (by simp) with h112 | h112
              · rcases m.htr 0 1 2 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 3 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h115 | h115
                    · linarith only [h110, h115, hlam]
                    · linarith only [h115, h82, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h114, hlam, p0_0]
                · linarith only [h113, h82, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h112, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h121 | h121
              · rcases m.htr 0 1 2 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 1 3 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h110, h124, hlam]
                    · linarith only [h124, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h123, hlam, p0_0]
                · linarith only [h122, h82, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h121, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h130 | h130
            · rcases p0_3 (m.d 0 6) (by simp) with h131 | h131
              · rcases m.htr 0 1 2 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 1 3 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h135 | h135
                      · linarith only [h131, h135, hlam]
                      · linarith only [h135, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h132, h134, h82, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h133, hlam, p0_0]
                · linarith only [h132, h82, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h131, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h142 | h142
              · rcases m.htr 0 1 2 (by decide) (by decide) with h143 | h143
                · rcases m.htr 0 1 3 (by decide) (by decide) with h144 | h144
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h146 | h146
                      · linarith only [h142, h146, hlam]
                      · linarith only [h146, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h143, h145, h82, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h144, hlam, p0_0]
                · linarith only [h143, h82, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h142, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h81, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h154 | h154
    · rcases p0_3 (m.d 0 2) (by simp) with h155 | h155
      · rcases p0_3 (m.d 0 3) (by simp) with h156 | h156
        · rcases p0_3 (m.d 0 4) (by simp) with h157 | h157
          · linarith only [h157, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h159 | h159
            · rcases p0_3 (m.d 0 6) (by simp) with h160 | h160
              · rcases m.htr 0 1 2 (by decide) (by decide) with h161 | h161
                · linarith only [h155, h161, hlam]
                · linarith only [h161, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h160, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h165 | h165
              · rcases m.htr 0 1 2 (by decide) (by decide) with h166 | h166
                · linarith only [h155, h166, hlam]
                · linarith only [h166, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h165, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h170 | h170
          · linarith only [h170, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · rcases p0_3 (m.d 0 6) (by simp) with h173 | h173
              · rcases m.htr 0 1 2 (by decide) (by decide) with h174 | h174
                · linarith only [h155, h174, hlam]
                · linarith only [h156, h174, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h173, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h178 | h178
              · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
                · linarith only [h155, h179, hlam]
                · linarith only [h179, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h178, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h183 | h183
        · rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
          · linarith only [h184, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h186 | h186
            · rcases p0_3 (m.d 0 6) (by simp) with h187 | h187
              · rcases m.htr 0 1 2 (by decide) (by decide) with h188 | h188
                · rcases m.htr 0 1 3 (by decide) (by decide) with h189 | h189
                  · linarith only [h183, h189, hlam]
                  · linarith only [h155, h189, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h155, h188, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h187, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h194 | h194
              · rcases m.htr 0 1 2 (by decide) (by decide) with h195 | h195
                · rcases m.htr 0 1 3 (by decide) (by decide) with h196 | h196
                  · linarith only [h183, h196, hlam]
                  · linarith only [h196, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h155, h195, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h194, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h201 | h201
          · linarith only [h201, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h203 | h203
            · rcases p0_3 (m.d 0 6) (by simp) with h204 | h204
              · rcases m.htr 0 1 2 (by decide) (by decide) with h205 | h205
                · rcases m.htr 0 1 3 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h208 | h208
                      · linarith only [h204, h208, hlam]
                      · linarith only [h183, h208, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h207, hlam, p0_0]
                  · linarith only [h155, h205, h206, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h155, h205, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h204, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h215 | h215
              · rcases m.htr 0 1 2 (by decide) (by decide) with h216 | h216
                · rcases m.htr 0 1 3 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h218 | h218
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h219 | h219
                      · linarith only [h215, h219, hlam]
                      · linarith only [h219, hc04, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h218, hlam, p0_0]
                  · linarith only [h155, h216, h217, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h155, h216, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h215, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h154, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h227 | h227
    · rcases p0_3 (m.d 0 2) (by simp) with h228 | h228
      · rcases p0_3 (m.d 0 3) (by simp) with h229 | h229
        · rcases p0_3 (m.d 0 4) (by simp) with h230 | h230
          · rcases p0_3 (m.d 0 5) (by simp) with h231 | h231
            · linarith only [h231, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h233 | h233
              · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
                · linarith only [h228, h234, hlam]
                · linarith only [h234, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h233, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h238 | h238
            · linarith only [h238, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h240 | h240
              · rcases m.htr 0 1 2 (by decide) (by decide) with h241 | h241
                · linarith only [h228, h241, hlam]
                · linarith only [h230, h241, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h240, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 0 5) (by simp) with h246 | h246
            · linarith only [h246, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h248 | h248
              · rcases m.htr 0 1 2 (by decide) (by decide) with h249 | h249
                · linarith only [h228, h249, hlam]
                · linarith only [h229, h249, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h248, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h253 | h253
            · linarith only [h253, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h255 | h255
              · rcases m.htr 0 1 2 (by decide) (by decide) with h256 | h256
                · linarith only [h228, h256, hlam]
                · linarith only [h245, h256, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h255, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h260 | h260
        · rcases p0_3 (m.d 0 4) (by simp) with h261 | h261
          · rcases p0_3 (m.d 0 5) (by simp) with h262 | h262
            · linarith only [h262, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h264 | h264
              · rcases m.htr 0 1 2 (by decide) (by decide) with h265 | h265
                · rcases m.htr 0 1 3 (by decide) (by decide) with h266 | h266
                  · linarith only [h260, h266, hlam]
                  · linarith only [h228, h266, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h228, h265, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h264, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h271 | h271
            · linarith only [h271, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h273 | h273
              · rcases m.htr 0 1 2 (by decide) (by decide) with h274 | h274
                · rcases m.htr 0 1 3 (by decide) (by decide) with h275 | h275
                  · linarith only [h260, h275, hlam]
                  · linarith only [h261, h275, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h228, h274, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h273, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 0 5) (by simp) with h281 | h281
            · linarith only [h281, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h283 | h283
              · rcases m.htr 0 1 2 (by decide) (by decide) with h284 | h284
                · rcases m.htr 0 1 3 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h286 | h286
                    · linarith only [h280, h286, hlam]
                    · linarith only [h260, h286, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h228, h284, h285, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h228, h284, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h283, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h292 | h292
            · linarith only [h292, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h294 | h294
              · rcases m.htr 0 1 2 (by decide) (by decide) with h295 | h295
                · rcases m.htr 0 1 3 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h297 | h297
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h298 | h298
                      · linarith only [h294, h298, hlam]
                      · linarith only [h260, h298, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h228, h295, h297, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h228, h295, h296, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h228, h295, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h294, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
    · linarith only [h227, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h307 | h307
    · linarith only [h307, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h309 | h309
      · rcases p0_3 (m.d 0 3) (by simp) with h310 | h310
        · rcases p0_3 (m.d 0 4) (by simp) with h311 | h311
          · rcases p0_3 (m.d 0 5) (by simp) with h312 | h312
            · rcases p0_3 (m.d 0 6) (by simp) with h313 | h313
              · rcases m.htr 0 1 2 (by decide) (by decide) with h314 | h314
                · linarith only [h314, hlam, p0_0]
                · linarith only [h314, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h313, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h318 | h318
              · rcases m.htr 0 1 2 (by decide) (by decide) with h319 | h319
                · linarith only [h319, hlam, p0_0]
                · linarith only [h319, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h318, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h323 | h323
            · rcases p0_3 (m.d 0 6) (by simp) with h324 | h324
              · rcases m.htr 0 1 2 (by decide) (by decide) with h325 | h325
                · linarith only [h325, hlam, p0_0]
                · linarith only [h325, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h324, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h329 | h329
              · rcases m.htr 0 1 2 (by decide) (by decide) with h330 | h330
                · linarith only [h330, hlam, p0_0]
                · linarith only [h330, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h329, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h334 | h334
          · rcases p0_3 (m.d 0 5) (by simp) with h335 | h335
            · rcases p0_3 (m.d 0 6) (by simp) with h336 | h336
              · rcases m.htr 0 1 2 (by decide) (by decide) with h337 | h337
                · linarith only [h337, hlam, p0_0]
                · linarith only [h337, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h336, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h341 | h341
              · rcases m.htr 0 1 2 (by decide) (by decide) with h342 | h342
                · linarith only [h342, hlam, p0_0]
                · linarith only [h342, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h341, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h346 | h346
            · rcases p0_3 (m.d 0 6) (by simp) with h347 | h347
              · rcases m.htr 0 1 2 (by decide) (by decide) with h348 | h348
                · linarith only [h348, hlam, p0_0]
                · linarith only [h348, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h347, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h352 | h352
              · rcases m.htr 0 1 2 (by decide) (by decide) with h353 | h353
                · linarith only [h353, hlam, p0_0]
                · linarith only [h353, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h352, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h309, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h359 | h359
    · rcases p0_3 (m.d 0 2) (by simp) with h360 | h360
      · rcases p0_3 (m.d 0 3) (by simp) with h361 | h361
        · linarith only [h361, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h363 | h363
          · rcases p0_3 (m.d 0 5) (by simp) with h364 | h364
            · rcases p0_3 (m.d 0 6) (by simp) with h365 | h365
              · rcases m.htr 0 1 2 (by decide) (by decide) with h366 | h366
                · rcases m.htr 0 1 3 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h368 | h368
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h369 | h369
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h370 | h370
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h371 | h371
                          · linarith only [h363, h371, hlam]
                          · linarith only [h371, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h370, hlam, p0_0]
                      · linarith only [h366, h367, h369, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h366, h367, h368, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h366, h367, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h366, hlam]
              · linarith only [h365, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h380 | h380
              · rcases m.htr 0 1 2 (by decide) (by decide) with h381 | h381
                · rcases m.htr 0 1 3 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h383 | h383
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h384 | h384
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h385 | h385
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h386 | h386
                          · linarith only [h363, h386, hlam]
                          · linarith only [h386, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h385, hlam, p0_0]
                      · linarith only [h381, h382, h384, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h381, h382, h383, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h381, h382, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h381, hlam]
              · linarith only [h359, h380, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h395 | h395
            · rcases p0_3 (m.d 0 6) (by simp) with h396 | h396
              · rcases m.htr 0 1 2 (by decide) (by decide) with h397 | h397
                · rcases m.htr 0 1 3 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h399 | h399
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h400 | h400
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h401 | h401
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h402 | h402
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h403 | h403
                            · linarith only [h396, h403, hlam]
                            · linarith only [h403, hc03, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h398, h402, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h401, hlam, p0_0]
                      · linarith only [h397, h398, h400, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h397, h398, h399, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h397, h398, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h397, hlam]
              · linarith only [h396, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h413 | h413
              · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
                · rcases m.htr 0 1 3 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h416 | h416
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h417 | h417
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h418 | h418
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h419 | h419
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h420 | h420
                            · linarith only [h413, h420, hlam]
                            · linarith only [h420, hc03, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h415, h419, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h418, hlam, p0_0]
                      · linarith only [h414, h415, h417, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h414, h415, h416, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h414, h415, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h414, hlam]
              · linarith only [h359, h413, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h360, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h431 | h431
      · rcases p0_3 (m.d 0 3) (by simp) with h432 | h432
        · linarith only [h432, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h434 | h434
          · rcases p0_3 (m.d 0 5) (by simp) with h435 | h435
            · rcases p0_3 (m.d 0 6) (by simp) with h436 | h436
              · rcases m.htr 0 1 2 (by decide) (by decide) with h437 | h437
                · linarith only [h359, h437, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h437, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h436, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h441 | h441
              · rcases m.htr 0 1 2 (by decide) (by decide) with h442 | h442
                · linarith only [h359, h442, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h442, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h441, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h446 | h446
            · rcases p0_3 (m.d 0 6) (by simp) with h447 | h447
              · rcases m.htr 0 1 2 (by decide) (by decide) with h448 | h448
                · linarith only [h359, h448, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h448, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h447, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h452 | h452
              · rcases m.htr 0 1 2 (by decide) (by decide) with h453 | h453
                · linarith only [h359, h453, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h359, h453, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h452, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h431, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h458 | h458
    · rcases p0_3 (m.d 0 2) (by simp) with h459 | h459
      · rcases p0_3 (m.d 0 3) (by simp) with h460 | h460
        · rcases p0_3 (m.d 0 4) (by simp) with h461 | h461
          · linarith only [h461, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h463 | h463
            · rcases p0_3 (m.d 0 6) (by simp) with h464 | h464
              · rcases m.htr 0 1 2 (by decide) (by decide) with h465 | h465
                · rcases m.htr 0 1 3 (by decide) (by decide) with h466 | h466
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h467 | h467
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h468 | h468
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h469 | h469
                        · linarith only [h460, h469, hlam]
                        · linarith only [h469, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                      · linarith only [h465, h467, h468, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h465, h467, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h465, h466, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h465, hlam]
              · linarith only [h464, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h477 | h477
              · rcases m.htr 0 1 2 (by decide) (by decide) with h478 | h478
                · rcases m.htr 0 1 3 (by decide) (by decide) with h479 | h479
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h480 | h480
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h481 | h481
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h482 | h482
                        · linarith only [h460, h482, hlam]
                        · linarith only [h482, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                      · linarith only [h478, h480, h481, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h478, h480, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h478, h479, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h478, hlam]
              · linarith only [h477, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h490 | h490
          · linarith only [h490, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h492 | h492
            · rcases p0_3 (m.d 0 6) (by simp) with h493 | h493
              · rcases m.htr 0 1 2 (by decide) (by decide) with h494 | h494
                · rcases m.htr 0 1 3 (by decide) (by decide) with h495 | h495
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h496 | h496
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h497 | h497
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h498 | h498
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h499 | h499
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h500 | h500
                            · linarith only [h493, h500, hlam]
                            · linarith only [h460, h500, hc03, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h499, hlam, p0_0]
                        · linarith only [h460, h495, h498, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h460, h494, h495, h497, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h460, h494, h495, h496, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h460, h494, h495, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h494, hlam]
              · linarith only [h493, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h510 | h510
              · rcases m.htr 0 1 2 (by decide) (by decide) with h511 | h511
                · rcases m.htr 0 1 3 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h514 | h514
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h515 | h515
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h516 | h516
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h517 | h517
                            · linarith only [h510, h517, hlam]
                            · linarith only [h517, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h516, hlam, p0_0]
                        · linarith only [h460, h512, h515, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h460, h511, h512, h514, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h460, h511, h512, h513, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h460, h511, h512, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h511, hlam]
              · linarith only [h510, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h459, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h528 | h528
      · rcases p0_3 (m.d 0 3) (by simp) with h529 | h529
        · rcases p0_3 (m.d 0 4) (by simp) with h530 | h530
          · linarith only [h530, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h532 | h532
            · rcases p0_3 (m.d 0 6) (by simp) with h533 | h533
              · rcases m.htr 0 1 2 (by decide) (by decide) with h534 | h534
                · linarith only [h458, h534, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h534, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h533, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h538 | h538
              · rcases m.htr 0 1 2 (by decide) (by decide) with h539 | h539
                · linarith only [h458, h539, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h539, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h538, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h543 | h543
          · linarith only [h543, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h545 | h545
            · rcases p0_3 (m.d 0 6) (by simp) with h546 | h546
              · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
                · linarith only [h458, h547, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h547, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h546, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h551 | h551
              · rcases m.htr 0 1 2 (by decide) (by decide) with h552 | h552
                · linarith only [h458, h552, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h458, h552, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h551, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h528, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h557 | h557
    · rcases p0_3 (m.d 0 2) (by simp) with h558 | h558
      · rcases p0_3 (m.d 0 3) (by simp) with h559 | h559
        · rcases p0_3 (m.d 0 4) (by simp) with h560 | h560
          · rcases p0_3 (m.d 0 5) (by simp) with h561 | h561
            · linarith only [h561, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h563 | h563
              · rcases m.htr 0 1 2 (by decide) (by decide) with h564 | h564
                · rcases m.htr 0 1 3 (by decide) (by decide) with h565 | h565
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h566 | h566
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h567 | h567
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h568 | h568
                        · linarith only [h559, h568, hlam]
                        · linarith only [h568, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                      · linarith only [h564, h567, hc05, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h564, h566, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h564, h565, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h557, h564, hlam]
              · linarith only [h563, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h576 | h576
            · linarith only [h576, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h578 | h578
              · rcases m.htr 0 1 2 (by decide) (by decide) with h579 | h579
                · rcases m.htr 0 1 3 (by decide) (by decide) with h580 | h580
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h581 | h581
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h582 | h582
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h583 | h583
                        · linarith only [h559, h583, hlam]
                        · linarith only [h560, h583, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                      · linarith only [h560, h579, h581, h582, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h560, h579, h581, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h560, h579, h580, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h557, h579, hlam]
              · linarith only [h578, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h591 | h591
          · rcases p0_3 (m.d 0 5) (by simp) with h592 | h592
            · linarith only [h592, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h594 | h594
              · rcases m.htr 0 1 2 (by decide) (by decide) with h595 | h595
                · rcases m.htr 0 1 3 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h597 | h597
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h598 | h598
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h599 | h599
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h600 | h600
                          · linarith only [h591, h600, hlam]
                          · linarith only [h559, h600, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h559, h596, h599, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h559, h595, h596, h598, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h559, h595, h596, h597, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h559, h595, h596, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h557, h595, hlam]
              · linarith only [h594, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h609 | h609
            · linarith only [h609, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h611 | h611
              · rcases m.htr 0 1 2 (by decide) (by decide) with h612 | h612
                · rcases m.htr 0 1 3 (by decide) (by decide) with h613 | h613
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h614 | h614
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h615 | h615
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h616 | h616
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h617 | h617
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h618 | h618
                            · linarith only [h611, h618, hlam]
                            · linarith only [h591, h618, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h559, h613, h617, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h559, h613, h616, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h559, h612, h613, h615, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h559, h612, h613, h614, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h559, h612, h613, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h557, h612, hlam]
              · linarith only [h611, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h558, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h629 | h629
      · rcases p0_3 (m.d 0 3) (by simp) with h630 | h630
        · rcases p0_3 (m.d 0 4) (by simp) with h631 | h631
          · rcases p0_3 (m.d 0 5) (by simp) with h632 | h632
            · linarith only [h632, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h634 | h634
              · rcases m.htr 0 1 2 (by decide) (by decide) with h635 | h635
                · linarith only [h557, h635, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h557, h635, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h634, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h639 | h639
            · linarith only [h639, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h641 | h641
              · rcases m.htr 0 1 2 (by decide) (by decide) with h642 | h642
                · linarith only [h557, h642, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h557, h642, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h641, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h646 | h646
          · rcases p0_3 (m.d 0 5) (by simp) with h647 | h647
            · linarith only [h647, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h649 | h649
              · rcases m.htr 0 1 2 (by decide) (by decide) with h650 | h650
                · linarith only [h557, h650, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h557, h650, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h649, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h654 | h654
            · linarith only [h654, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h656 | h656
              · rcases m.htr 0 1 2 (by decide) (by decide) with h657 | h657
                · linarith only [h557, h657, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h557, h657, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h656, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
      · linarith only [h629, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h663 | h663
    · linarith only [h663, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h665 | h665
      · rcases p0_3 (m.d 0 3) (by simp) with h666 | h666
        · rcases p0_3 (m.d 0 4) (by simp) with h667 | h667
          · rcases p0_3 (m.d 0 5) (by simp) with h668 | h668
            · rcases p0_3 (m.d 0 6) (by simp) with h669 | h669
              · rcases m.htr 0 1 2 (by decide) (by decide) with h670 | h670
                · linarith only [h670, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h670, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h665, h669, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h674 | h674
              · rcases m.htr 0 1 2 (by decide) (by decide) with h675 | h675
                · linarith only [h665, h675, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h675, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h665, h674, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h679 | h679
            · rcases p0_3 (m.d 0 6) (by simp) with h680 | h680
              · rcases m.htr 0 1 2 (by decide) (by decide) with h681 | h681
                · linarith only [h665, h681, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h681, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h665, h680, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h685 | h685
              · rcases m.htr 0 1 2 (by decide) (by decide) with h686 | h686
                · linarith only [h665, h686, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h686, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h665, h685, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h666, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h691 | h691
        · rcases p0_3 (m.d 0 4) (by simp) with h692 | h692
          · rcases p0_3 (m.d 0 5) (by simp) with h693 | h693
            · rcases p0_3 (m.d 0 6) (by simp) with h694 | h694
              · rcases m.htr 0 1 2 (by decide) (by decide) with h695 | h695
                · linarith only [h695, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h695, hlam]
              · linarith only [h694, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h699 | h699
              · rcases m.htr 0 1 2 (by decide) (by decide) with h700 | h700
                · linarith only [h700, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h700, hlam]
              · linarith only [h699, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h704 | h704
            · rcases p0_3 (m.d 0 6) (by simp) with h705 | h705
              · rcases m.htr 0 1 2 (by decide) (by decide) with h706 | h706
                · linarith only [h706, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h706, hlam]
              · linarith only [h705, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h710 | h710
              · rcases m.htr 0 1 2 (by decide) (by decide) with h711 | h711
                · linarith only [h711, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h665, h711, hlam]
              · linarith only [h710, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h691, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h716 | h716
    · rcases p0_3 (m.d 0 2) (by simp) with h717 | h717
      · linarith only [h717, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h719 | h719
        · rcases p0_3 (m.d 0 4) (by simp) with h720 | h720
          · rcases p0_3 (m.d 0 5) (by simp) with h721 | h721
            · rcases p0_3 (m.d 0 6) (by simp) with h722 | h722
              · rcases m.htr 0 1 2 (by decide) (by decide) with h723 | h723
                · rcases m.htr 0 1 3 (by decide) (by decide) with h724 | h724
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h725 | h725
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h726 | h726
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h727 | h727
                        · linarith only [h727, hlam, p0_0]
                        · linarith only [h727, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h723, h724, h726, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h723, h724, h725, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h716, h724, hlam]
                · linarith only [h716, h723, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h716, h722, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h735 | h735
              · rcases m.htr 0 1 2 (by decide) (by decide) with h736 | h736
                · rcases m.htr 0 1 3 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h739 | h739
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h740 | h740
                        · linarith only [h740, hlam, p0_0]
                        · linarith only [h740, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h736, h737, h739, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h736, h737, h738, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h716, h737, hlam]
                · linarith only [h716, h736, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h716, h735, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h748 | h748
            · rcases p0_3 (m.d 0 6) (by simp) with h749 | h749
              · rcases m.htr 0 1 2 (by decide) (by decide) with h750 | h750
                · rcases m.htr 0 1 3 (by decide) (by decide) with h751 | h751
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h752 | h752
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h753 | h753
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h754 | h754
                        · linarith only [h754, hlam, p0_0]
                        · linarith only [h754, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h750, h751, h753, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h750, h751, h752, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h716, h751, hlam]
                · linarith only [h716, h750, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h716, h749, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h762 | h762
              · rcases m.htr 0 1 2 (by decide) (by decide) with h763 | h763
                · rcases m.htr 0 1 3 (by decide) (by decide) with h764 | h764
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h765 | h765
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h766 | h766
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h767 | h767
                        · linarith only [h767, hlam, p0_0]
                        · linarith only [h767, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h763, h764, h766, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h763, h764, h765, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h716, h764, hlam]
                · linarith only [h716, h763, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h716, h762, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h719, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h776 | h776
      · linarith only [h776, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h778 | h778
        · rcases p0_3 (m.d 0 4) (by simp) with h779 | h779
          · rcases p0_3 (m.d 0 5) (by simp) with h780 | h780
            · rcases p0_3 (m.d 0 6) (by simp) with h781 | h781
              · rcases m.htr 0 1 2 (by decide) (by decide) with h782 | h782
                · linarith only [h716, h782, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h784 | h784
                  · linarith only [h782, h784, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h782, h784, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h781, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h788 | h788
              · rcases m.htr 0 1 2 (by decide) (by decide) with h789 | h789
                · linarith only [h716, h789, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h791 | h791
                  · linarith only [h789, h791, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h789, h791, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h788, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h795 | h795
            · rcases p0_3 (m.d 0 6) (by simp) with h796 | h796
              · rcases m.htr 0 1 2 (by decide) (by decide) with h797 | h797
                · linarith only [h716, h797, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h799 | h799
                  · linarith only [h797, h799, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h797, h799, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h796, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h803 | h803
              · rcases m.htr 0 1 2 (by decide) (by decide) with h804 | h804
                · linarith only [h716, h804, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h806 | h806
                  · linarith only [h804, h806, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h804, h806, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h803, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h778, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h812 | h812
    · rcases p0_3 (m.d 0 2) (by simp) with h813 | h813
      · rcases p0_3 (m.d 0 3) (by simp) with h814 | h814
        · rcases p0_3 (m.d 0 4) (by simp) with h815 | h815
          · linarith only [h815, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h817 | h817
            · rcases p0_3 (m.d 0 6) (by simp) with h818 | h818
              · rcases m.htr 0 1 2 (by decide) (by decide) with h819 | h819
                · rcases m.htr 0 1 3 (by decide) (by decide) with h820 | h820
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h821 | h821
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h822 | h822
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h823 | h823
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h824 | h824
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h825 | h825
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h826 | h826
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h827 | h827
                                · linarith only [h818, h827, hlam]
                                · linarith only [h821, h827, hc14, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                              · linarith only [h826, hlam, p0_0]
                            · linarith only [h821, h823, h825, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h821, h823, h824, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h813, h823, hlam]
                      · linarith only [h820, h821, h822, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h813, h819, h821, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h812, h820, hlam]
                · linarith only [h812, h819, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h812, h818, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h839 | h839
              · rcases m.htr 0 1 2 (by decide) (by decide) with h840 | h840
                · rcases m.htr 0 1 3 (by decide) (by decide) with h841 | h841
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h842 | h842
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h843 | h843
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h844 | h844
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h845 | h845
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h846 | h846
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h847 | h847
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h848 | h848
                                · linarith only [h839, h848, hlam]
                                · linarith only [h848, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                              · linarith only [h847, hlam, p0_0]
                            · linarith only [h842, h844, h846, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h842, h844, h845, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h813, h844, hlam]
                      · linarith only [h841, h842, h843, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h841, h842, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h812, h841, hlam]
                · linarith only [h812, h840, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h812, h839, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h814, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h861 | h861
        · rcases p0_3 (m.d 0 4) (by simp) with h862 | h862
          · linarith only [h862, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h864 | h864
            · rcases p0_3 (m.d 0 6) (by simp) with h865 | h865
              · rcases m.htr 0 1 2 (by decide) (by decide) with h866 | h866
                · rcases m.htr 0 1 3 (by decide) (by decide) with h867 | h867
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h868 | h868
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h869 | h869
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h870 | h870
                        · linarith only [h813, h867, h870, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h813, h866, h870, hc12, hc23, hlam, hphi, p0_1]
                      · linarith only [h813, h866, h867, h869, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h813, h866, h867, h868, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h812, h867, hlam]
                · linarith only [h812, h813, h866, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h812, h865, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h878 | h878
              · rcases m.htr 0 1 2 (by decide) (by decide) with h879 | h879
                · rcases m.htr 0 1 3 (by decide) (by decide) with h880 | h880
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h881 | h881
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h882 | h882
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h883 | h883
                        · linarith only [h813, h880, h883, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h813, h883, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h813, h879, h880, h882, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h813, h879, h880, h881, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h812, h880, hlam]
                · linarith only [h812, h813, h879, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h812, h878, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h861, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h892 | h892
      · rcases p0_3 (m.d 0 3) (by simp) with h893 | h893
        · rcases p0_3 (m.d 0 4) (by simp) with h894 | h894
          · linarith only [h894, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h896 | h896
            · rcases p0_3 (m.d 0 6) (by simp) with h897 | h897
              · rcases m.htr 0 1 2 (by decide) (by decide) with h898 | h898
                · linarith only [h812, h898, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h812, h892, h898, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h892, h897, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h902 | h902
              · rcases m.htr 0 1 2 (by decide) (by decide) with h903 | h903
                · linarith only [h812, h892, h903, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h812, h892, h903, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h892, h902, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h893, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h908 | h908
        · rcases p0_3 (m.d 0 4) (by simp) with h909 | h909
          · linarith only [h909, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h911 | h911
            · rcases p0_3 (m.d 0 6) (by simp) with h912 | h912
              · rcases m.htr 0 1 2 (by decide) (by decide) with h913 | h913
                · linarith only [h812, h913, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h915 | h915
                  · linarith only [h892, h913, h915, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h892, h913, h915, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h912, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h919 | h919
              · rcases m.htr 0 1 2 (by decide) (by decide) with h920 | h920
                · linarith only [h812, h920, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h922 | h922
                  · linarith only [h892, h920, h922, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h892, h920, h922, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h919, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h908, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h927 | h927
    · rcases p0_3 (m.d 0 2) (by simp) with h928 | h928
      · rcases p0_3 (m.d 0 3) (by simp) with h929 | h929
        · rcases p0_3 (m.d 0 4) (by simp) with h930 | h930
          · rcases p0_3 (m.d 0 5) (by simp) with h931 | h931
            · linarith only [h931, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h933 | h933
              · rcases m.htr 0 1 2 (by decide) (by decide) with h934 | h934
                · rcases m.htr 0 1 3 (by decide) (by decide) with h935 | h935
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h936 | h936
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h937 | h937
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h938 | h938
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h939 | h939
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h940 | h940
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h941 | h941
                              · linarith only [h930, h941, hlam]
                              · linarith only [h941, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                            · linarith only [h938, h940, hc05, hc26, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                          · linarith only [h938, h939, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h928, h938, hlam]
                      · linarith only [h935, h937, hc05, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h928, h934, h936, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h927, h935, hlam]
                · linarith only [h927, h934, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h927, h933, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h952 | h952
            · linarith only [h952, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h954 | h954
              · rcases m.htr 0 1 2 (by decide) (by decide) with h955 | h955
                · rcases m.htr 0 1 3 (by decide) (by decide) with h956 | h956
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h957 | h957
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h958 | h958
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h959 | h959
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h960 | h960
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h961 | h961
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h962 | h962
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h963 | h963
                                · linarith only [h954, h963, hlam]
                                · linarith only [h930, h963, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                              · linarith only [h930, h957, h962, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                            · linarith only [h930, h957, h959, h961, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h930, h957, h959, h960, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h928, h959, hlam]
                      · linarith only [h930, h956, h957, h958, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h930, h956, h957, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h927, h956, hlam]
                · linarith only [h927, h930, h955, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h927, h954, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h929, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h976 | h976
        · rcases p0_3 (m.d 0 4) (by simp) with h977 | h977
          · rcases p0_3 (m.d 0 5) (by simp) with h978 | h978
            · linarith only [h978, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h980 | h980
              · rcases m.htr 0 1 2 (by decide) (by decide) with h981 | h981
                · rcases m.htr 0 1 3 (by decide) (by decide) with h982 | h982
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h983 | h983
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h984 | h984
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h985 | h985
                        · linarith only [h928, h982, h985, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h928, h981, h985, hc12, hc23, hlam, hphi, p0_1]
                      · linarith only [h928, h981, h982, h984, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h928, h981, h982, h983, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h927, h982, hlam]
                · linarith only [h927, h928, h981, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h927, h980, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h993 | h993
            · linarith only [h993, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h995 | h995
              · rcases m.htr 0 1 2 (by decide) (by decide) with h996 | h996
                · rcases m.htr 0 1 3 (by decide) (by decide) with h997 | h997
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h998 | h998
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h999 | h999
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1000 | h1000
                        · linarith only [h1000, h928, h997, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1000, h928, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h928, h996, h997, h999, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h928, h996, h997, h998, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h927, h997, hlam]
                · linarith only [h927, h928, h996, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h927, h995, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h976, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1009 | h1009
      · rcases p0_3 (m.d 0 3) (by simp) with h1010 | h1010
        · rcases p0_3 (m.d 0 4) (by simp) with h1011 | h1011
          · rcases p0_3 (m.d 0 5) (by simp) with h1012 | h1012
            · linarith only [h1012, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1014 | h1014
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1015 | h1015
                · linarith only [h1015, h927, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1009, h1015, h927, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1009, h1014, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1019 | h1019
            · linarith only [h1019, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1021 | h1021
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1022 | h1022
                · linarith only [h1009, h1022, h927, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1009, h1022, h927, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1009, h1021, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h1010, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1027 | h1027
        · rcases p0_3 (m.d 0 4) (by simp) with h1028 | h1028
          · rcases p0_3 (m.d 0 5) (by simp) with h1029 | h1029
            · linarith only [h1029, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1031 | h1031
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1032 | h1032
                · linarith only [h1032, h927, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1034 | h1034
                  · linarith only [h1009, h1032, h1034, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1009, h1032, h1034, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1031, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1038 | h1038
            · linarith only [h1038, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1040 | h1040
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1041 | h1041
                · linarith only [h1041, h927, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1043 | h1043
                  · linarith only [h1009, h1041, h1043, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1009, h1041, h1043, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1040, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
        · linarith only [h1027, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1049 | h1049
    · linarith only [h1049, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1051 | h1051
      · rcases p0_3 (m.d 0 3) (by simp) with h1052 | h1052
        · rcases p0_3 (m.d 0 4) (by simp) with h1053 | h1053
          · rcases p0_3 (m.d 0 5) (by simp) with h1054 | h1054
            · rcases p0_3 (m.d 0 6) (by simp) with h1055 | h1055
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1056 | h1056
                · linarith only [h1051, h1056, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1056, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1051, h1055, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1060 | h1060
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1061 | h1061
                · linarith only [h1051, h1061, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1061, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1051, h1060, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1053, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1066 | h1066
          · rcases p0_3 (m.d 0 5) (by simp) with h1067 | h1067
            · rcases p0_3 (m.d 0 6) (by simp) with h1068 | h1068
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1069 | h1069
                · linarith only [h1051, h1069, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1069, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1051, h1068, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1073 | h1073
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1074 | h1074
                · linarith only [h1051, h1074, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1074, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1051, h1073, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1066, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1079 | h1079
        · rcases p0_3 (m.d 0 4) (by simp) with h1080 | h1080
          · rcases p0_3 (m.d 0 5) (by simp) with h1081 | h1081
            · rcases p0_3 (m.d 0 6) (by simp) with h1082 | h1082
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1083 | h1083
                · linarith only [h1083, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1083, hlam]
              · linarith only [h1082, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1087 | h1087
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1088 | h1088
                · linarith only [h1088, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1088, hlam]
              · linarith only [h1087, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1080, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1093 | h1093
          · rcases p0_3 (m.d 0 5) (by simp) with h1094 | h1094
            · rcases p0_3 (m.d 0 6) (by simp) with h1095 | h1095
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1096 | h1096
                · linarith only [h1096, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1096, hlam]
              · linarith only [h1095, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1100 | h1100
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1101 | h1101
                · linarith only [h1101, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1051, h1101, hlam]
              · linarith only [h1100, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1093, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1106 | h1106
    · rcases p0_3 (m.d 0 2) (by simp) with h1107 | h1107
      · linarith only [h1107, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1109 | h1109
        · rcases p0_3 (m.d 0 4) (by simp) with h1110 | h1110
          · rcases p0_3 (m.d 0 5) (by simp) with h1111 | h1111
            · rcases p0_3 (m.d 0 6) (by simp) with h1112 | h1112
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1114 | h1114
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1115 | h1115
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1116 | h1116
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1117 | h1117
                        · linarith only [h1109, h1114, h1117, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1109, h1117, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h1113, h1115, h1116, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1106, h1115, hlam]
                  · linarith only [h1106, h1113, h1114, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1106, h1113, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1106, h1112, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1125 | h1125
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1126 | h1126
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1127 | h1127
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1128 | h1128
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1129 | h1129
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1130 | h1130
                        · linarith only [h1109, h1127, h1130, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1109, h1130, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h1126, h1128, h1129, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1106, h1128, hlam]
                  · linarith only [h1106, h1126, h1127, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1106, h1126, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1106, h1125, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1110, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1139 | h1139
          · rcases p0_3 (m.d 0 5) (by simp) with h1140 | h1140
            · rcases p0_3 (m.d 0 6) (by simp) with h1141 | h1141
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1142 | h1142
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1143 | h1143
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1144 | h1144
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1145 | h1145
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1146 | h1146
                        · linarith only [h1144, h1146, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1109, h1146, hlam]
                      · linarith only [h1144, h1145, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1106, h1144, hlam]
                  · linarith only [h1106, h1142, h1143, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1106, h1142, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1106, h1141, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1154 | h1154
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1155 | h1155
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1156 | h1156
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1157 | h1157
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1158 | h1158
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1159 | h1159
                        · linarith only [h1157, h1159, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1109, h1159, hlam]
                      · linarith only [h1157, h1158, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1106, h1157, hlam]
                  · linarith only [h1106, h1155, h1156, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1106, h1155, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1106, h1154, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1139, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1168 | h1168
      · linarith only [h1168, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1170 | h1170
        · rcases p0_3 (m.d 0 4) (by simp) with h1171 | h1171
          · rcases p0_3 (m.d 0 5) (by simp) with h1172 | h1172
            · rcases p0_3 (m.d 0 6) (by simp) with h1173 | h1173
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1174 | h1174
                · linarith only [h1106, h1174, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1176 | h1176
                  · linarith only [h1174, h1176, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1170, h1174, h1176, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1173, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1180 | h1180
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1181 | h1181
                · linarith only [h1106, h1181, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1183 | h1183
                  · linarith only [h1181, h1183, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1170, h1181, h1183, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1180, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1171, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1188 | h1188
          · rcases p0_3 (m.d 0 5) (by simp) with h1189 | h1189
            · rcases p0_3 (m.d 0 6) (by simp) with h1190 | h1190
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1191 | h1191
                · linarith only [h1106, h1191, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1193 | h1193
                  · linarith only [h1191, h1193, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1195 | h1195
                    · linarith only [h1191, h1195, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1191, h1195, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1190, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1199 | h1199
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1200 | h1200
                · linarith only [h1106, h1200, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1202 | h1202
                  · linarith only [h1200, h1202, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1204 | h1204
                    · linarith only [h1200, h1204, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1200, h1204, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1199, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1188, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1209 | h1209
    · rcases p0_3 (m.d 0 2) (by simp) with h1210 | h1210
      · rcases p0_3 (m.d 0 3) (by simp) with h1211 | h1211
        · linarith only [h1211, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1213 | h1213
          · rcases p0_3 (m.d 0 5) (by simp) with h1214 | h1214
            · rcases p0_3 (m.d 0 6) (by simp) with h1215 | h1215
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1216 | h1216
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1217 | h1217
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1218 | h1218
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1219 | h1219
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1220 | h1220
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1221 | h1221
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1222 | h1222
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1223 | h1223
                              · linarith only [h1223, hlam, p0_0]
                              · linarith only [h1217, h1223, hc13, hc34, hlam, hphi, p0_1]
                            · linarith only [h1217, h1221, h1222, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1210, h1221, hlam]
                        · linarith only [h1210, h1217, h1220, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1217, h1218, h1219, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1209, h1218, hlam]
                  · linarith only [h1209, h1217, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1209, h1216, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1209, h1215, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1234 | h1234
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1235 | h1235
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1236 | h1236
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1237 | h1237
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1238 | h1238
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1239 | h1239
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1240 | h1240
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1241 | h1241
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1242 | h1242
                              · linarith only [h1242, hlam, p0_0]
                              · linarith only [h1242, hc03, hc34, hlam, hphi, p0_1]
                            · linarith only [h1236, h1240, h1241, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1210, h1240, hlam]
                        · linarith only [h1210, h1236, h1239, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1236, h1237, h1238, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1209, h1237, hlam]
                  · linarith only [h1210, h1235, h1236, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1209, h1235, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1209, h1234, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1213, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1254 | h1254
        · linarith only [h1254, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1256 | h1256
          · rcases p0_3 (m.d 0 5) (by simp) with h1257 | h1257
            · rcases p0_3 (m.d 0 6) (by simp) with h1258 | h1258
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1259 | h1259
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1260 | h1260
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1261 | h1261
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1262 | h1262
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1263 | h1263
                        · linarith only [h1210, h1263, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1265 | h1265
                          · linarith only [h1261, h1263, h1265, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1259, h1263, h1265, hc12, hc24, hlam, hphi, p0_1]
                      · linarith only [h1261, h1262, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1209, h1261, hlam]
                  · linarith only [h1209, h1210, h1259, h1260, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1209, h1210, h1259, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1209, h1258, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1273 | h1273
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1274 | h1274
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1275 | h1275
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1276 | h1276
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1277 | h1277
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1278 | h1278
                        · linarith only [h1210, h1278, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1280 | h1280
                          · linarith only [h1276, h1278, h1280, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1278, h1280, hc02, hc24, hlam, hphi, p0_1]
                      · linarith only [h1276, h1277, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1209, h1276, hlam]
                  · linarith only [h1209, h1210, h1274, h1275, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1209, h1210, h1274, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1209, h1273, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1256, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1289 | h1289
      · rcases p0_3 (m.d 0 3) (by simp) with h1290 | h1290
        · linarith only [h1290, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1292 | h1292
          · rcases p0_3 (m.d 0 5) (by simp) with h1293 | h1293
            · rcases p0_3 (m.d 0 6) (by simp) with h1294 | h1294
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1295 | h1295
                · linarith only [h1209, h1295, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1209, h1289, h1295, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1289, h1294, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1299 | h1299
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1300 | h1300
                · linarith only [h1209, h1289, h1300, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1209, h1289, h1300, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1289, h1299, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1292, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1305 | h1305
        · linarith only [h1305, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1307 | h1307
          · rcases p0_3 (m.d 0 5) (by simp) with h1308 | h1308
            · rcases p0_3 (m.d 0 6) (by simp) with h1309 | h1309
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1310 | h1310
                · linarith only [h1209, h1310, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1312 | h1312
                  · linarith only [h1209, h1312, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1314 | h1314
                    · linarith only [h1289, h1310, h1314, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1289, h1310, h1314, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1309, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1318 | h1318
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1319 | h1319
                · linarith only [h1209, h1319, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1321 | h1321
                  · linarith only [h1209, h1321, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1323 | h1323
                    · linarith only [h1289, h1319, h1323, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1289, h1319, h1323, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1318, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1307, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1329 | h1329
    · rcases p0_3 (m.d 0 2) (by simp) with h1330 | h1330
      · rcases p0_3 (m.d 0 3) (by simp) with h1331 | h1331
        · rcases p0_3 (m.d 0 4) (by simp) with h1332 | h1332
          · rcases p0_3 (m.d 0 5) (by simp) with h1333 | h1333
            · linarith only [h1333, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1335 | h1335
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1336 | h1336
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1337 | h1337
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1338 | h1338
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1339 | h1339
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1340 | h1340
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1341 | h1341
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1342 | h1342
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1343 | h1343
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h1344 | h1344
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1345 | h1345
                                  · rcases m.htr 0 4 6 (by decide) (by decide) with h1346 | h1346
                                    · linarith only [h1335, h1346, hlam]
                                    · linarith only [h1345, h1346, hc45, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, p0_1]
                                  · linarith only [h1345, hlam, p0_0]
                                · linarith only [h1343, h1344, hc05, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                              · linarith only [h1331, h1343, hlam]
                            · linarith only [h1341, h1342, hc05, hc26, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                          · linarith only [h1330, h1341, hlam]
                        · linarith only [h1330, h1340, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                      · linarith only [h1338, h1339, hc05, hc16, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h1329, h1338, hlam]
                  · linarith only [h1329, h1337, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1329, h1336, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h1329, h1335, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1332, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1361 | h1361
          · rcases p0_3 (m.d 0 5) (by simp) with h1362 | h1362
            · linarith only [h1362, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1364 | h1364
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1365 | h1365
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1366 | h1366
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1367 | h1367
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1368 | h1368
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1369 | h1369
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1370 | h1370
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1371 | h1371
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1372 | h1372
                              · linarith only [h1331, h1365, h1370, h1372, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1331, h1366, h1372, hc13, hc34, hlam, hphi, p0_1]
                            · linarith only [h1331, h1366, h1370, h1371, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1330, h1370, hlam]
                        · linarith only [h1330, h1331, h1366, h1369, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1331, h1366, h1367, h1368, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1329, h1367, hlam]
                  · linarith only [h1330, h1331, h1365, h1366, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1329, h1331, h1365, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1329, h1364, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1361, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1384 | h1384
        · rcases p0_3 (m.d 0 4) (by simp) with h1385 | h1385
          · rcases p0_3 (m.d 0 5) (by simp) with h1386 | h1386
            · linarith only [h1386, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1388 | h1388
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1389 | h1389
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1390 | h1390
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1391 | h1391
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1392 | h1392
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1393 | h1393
                        · linarith only [h1330, h1384, h1390, h1393, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1330, h1384, h1389, h1393, hc12, hc23, hlam, hphi, p0_1]
                      · linarith only [h1330, h1384, h1389, h1390, h1392, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1329, h1391, hlam]
                  · linarith only [h1329, h1330, h1389, h1390, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1329, h1330, h1389, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1329, h1388, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1385, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1402 | h1402
          · rcases p0_3 (m.d 0 5) (by simp) with h1403 | h1403
            · linarith only [h1403, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1405 | h1405
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1406 | h1406
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1407 | h1407
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1408 | h1408
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1409 | h1409
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1410 | h1410
                        · linarith only [h1330, h1408, h1410, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1412 | h1412
                          · linarith only [h1384, h1408, h1410, h1412, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1384, h1410, h1412, hc02, hc24, hlam, hphi, p0_1]
                      · linarith only [h1384, h1408, h1409, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1329, h1408, hlam]
                  · linarith only [h1329, h1330, h1406, h1407, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1329, h1330, h1406, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1329, h1405, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1402, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1421 | h1421
      · rcases p0_3 (m.d 0 3) (by simp) with h1422 | h1422
        · rcases p0_3 (m.d 0 4) (by simp) with h1423 | h1423
          · rcases p0_3 (m.d 0 5) (by simp) with h1424 | h1424
            · linarith only [h1424, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1426 | h1426
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1427 | h1427
                · linarith only [h1329, h1427, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1329, h1421, h1427, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1421, h1426, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1423, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1432 | h1432
          · rcases p0_3 (m.d 0 5) (by simp) with h1433 | h1433
            · linarith only [h1433, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1435 | h1435
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1436 | h1436
                · linarith only [h1329, h1421, h1436, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1329, h1421, h1436, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1421, h1435, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1432, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1441 | h1441
        · rcases p0_3 (m.d 0 4) (by simp) with h1442 | h1442
          · rcases p0_3 (m.d 0 5) (by simp) with h1443 | h1443
            · linarith only [h1443, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1445 | h1445
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1446 | h1446
                · linarith only [h1329, h1446, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1448 | h1448
                  · linarith only [h1421, h1446, h1448, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1421, h1441, h1446, h1448, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1445, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1442, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1453 | h1453
          · rcases p0_3 (m.d 0 5) (by simp) with h1454 | h1454
            · linarith only [h1454, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1456 | h1456
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1457 | h1457
                · linarith only [h1329, h1457, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1459 | h1459
                  · linarith only [h1421, h1457, h1459, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1461 | h1461
                    · linarith only [h1421, h1457, h1461, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1421, h1457, h1461, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1456, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
          · linarith only [h1453, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1467 | h1467
    · linarith only [h1467, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1469 | h1469
      · rcases p0_3 (m.d 0 3) (by simp) with h1470 | h1470
        · rcases p0_3 (m.d 0 4) (by simp) with h1471 | h1471
          · rcases p0_3 (m.d 0 5) (by simp) with h1472 | h1472
            · rcases p0_3 (m.d 0 6) (by simp) with h1473 | h1473
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1474 | h1474
                · linarith only [h1469, h1474, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1474, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1469, h1473, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1472, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1479 | h1479
            · rcases p0_3 (m.d 0 6) (by simp) with h1480 | h1480
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1481 | h1481
                · linarith only [h1469, h1481, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1481, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1469, h1480, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1479, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1486 | h1486
          · rcases p0_3 (m.d 0 5) (by simp) with h1487 | h1487
            · rcases p0_3 (m.d 0 6) (by simp) with h1488 | h1488
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1489 | h1489
                · linarith only [h1469, h1489, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1489, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1469, h1488, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1487, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1494 | h1494
            · rcases p0_3 (m.d 0 6) (by simp) with h1495 | h1495
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1496 | h1496
                · linarith only [h1469, h1496, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1496, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1469, h1495, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1494, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1501 | h1501
        · rcases p0_3 (m.d 0 4) (by simp) with h1502 | h1502
          · rcases p0_3 (m.d 0 5) (by simp) with h1503 | h1503
            · rcases p0_3 (m.d 0 6) (by simp) with h1504 | h1504
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1505 | h1505
                · linarith only [h1505, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1505, hlam]
              · linarith only [h1504, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1503, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1510 | h1510
            · rcases p0_3 (m.d 0 6) (by simp) with h1511 | h1511
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1512 | h1512
                · linarith only [h1512, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1512, hlam]
              · linarith only [h1511, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1510, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1517 | h1517
          · rcases p0_3 (m.d 0 5) (by simp) with h1518 | h1518
            · rcases p0_3 (m.d 0 6) (by simp) with h1519 | h1519
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1520 | h1520
                · linarith only [h1520, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1520, hlam]
              · linarith only [h1519, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1518, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1525 | h1525
            · rcases p0_3 (m.d 0 6) (by simp) with h1526 | h1526
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1527 | h1527
                · linarith only [h1527, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1469, h1527, hlam]
              · linarith only [h1526, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1525, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1532 | h1532
    · rcases p0_3 (m.d 0 2) (by simp) with h1533 | h1533
      · linarith only [h1533, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1535 | h1535
        · rcases p0_3 (m.d 0 4) (by simp) with h1536 | h1536
          · rcases p0_3 (m.d 0 5) (by simp) with h1537 | h1537
            · rcases p0_3 (m.d 0 6) (by simp) with h1538 | h1538
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1539 | h1539
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1540 | h1540
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1541 | h1541
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1542 | h1542
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1543 | h1543
                        · linarith only [h1535, h1540, h1543, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1535, h1543, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h1535, h1539, h1540, h1542, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1535, h1539, h1540, h1541, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1532, h1539, h1540, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1532, h1539, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1532, h1538, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1537, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1552 | h1552
            · rcases p0_3 (m.d 0 6) (by simp) with h1553 | h1553
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1554 | h1554
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1555 | h1555
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1556 | h1556
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1557 | h1557
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1558 | h1558
                        · linarith only [h1535, h1555, h1558, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1535, h1558, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h1535, h1554, h1555, h1557, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1535, h1554, h1555, h1556, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1532, h1554, h1555, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1532, h1554, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1532, h1553, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1552, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1567 | h1567
          · rcases p0_3 (m.d 0 5) (by simp) with h1568 | h1568
            · rcases p0_3 (m.d 0 6) (by simp) with h1569 | h1569
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1570 | h1570
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1571 | h1571
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1572 | h1572
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1573 | h1573
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1574 | h1574
                        · linarith only [h1567, h1572, h1574, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1535, h1574, hlam]
                      · linarith only [h1567, h1572, h1573, hc02, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1532, h1570, h1572, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1532, h1570, h1571, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1532, h1570, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1532, h1569, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1568, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1583 | h1583
            · rcases p0_3 (m.d 0 6) (by simp) with h1584 | h1584
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1585 | h1585
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1586 | h1586
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1587 | h1587
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1588 | h1588
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1589 | h1589
                        · linarith only [h1584, h1588, h1589, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1535, h1589, hlam]
                      · linarith only [h1532, h1585, h1588, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1532, h1585, h1587, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1532, h1585, h1586, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1532, h1585, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1532, h1584, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1583, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1598 | h1598
      · linarith only [h1598, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1600 | h1600
        · rcases p0_3 (m.d 0 4) (by simp) with h1601 | h1601
          · rcases p0_3 (m.d 0 5) (by simp) with h1602 | h1602
            · rcases p0_3 (m.d 0 6) (by simp) with h1603 | h1603
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1604 | h1604
                · linarith only [h1532, h1604, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1606 | h1606
                  · linarith only [h1604, h1606, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1600, h1604, h1606, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1603, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1602, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1611 | h1611
            · rcases p0_3 (m.d 0 6) (by simp) with h1612 | h1612
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1613 | h1613
                · linarith only [h1532, h1613, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1615 | h1615
                  · linarith only [h1613, h1615, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1600, h1613, h1615, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1612, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1611, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1620 | h1620
          · rcases p0_3 (m.d 0 5) (by simp) with h1621 | h1621
            · rcases p0_3 (m.d 0 6) (by simp) with h1622 | h1622
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1623 | h1623
                · linarith only [h1532, h1623, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1625 | h1625
                  · linarith only [h1623, h1625, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1627 | h1627
                    · linarith only [h1623, h1627, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1620, h1623, h1627, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1622, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1621, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1632 | h1632
            · rcases p0_3 (m.d 0 6) (by simp) with h1633 | h1633
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1634 | h1634
                · linarith only [h1532, h1634, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1636 | h1636
                  · linarith only [h1634, h1636, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1638 | h1638
                    · linarith only [h1634, h1638, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1640 | h1640
                      · linarith only [h1634, h1640, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h1633, h1634, h1640, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h1633, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1632, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1645 | h1645
    · rcases p0_3 (m.d 0 2) (by simp) with h1646 | h1646
      · rcases p0_3 (m.d 0 3) (by simp) with h1647 | h1647
        · linarith only [h1647, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1649 | h1649
          · rcases p0_3 (m.d 0 5) (by simp) with h1650 | h1650
            · rcases p0_3 (m.d 0 6) (by simp) with h1651 | h1651
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1652 | h1652
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1653 | h1653
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1654 | h1654
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1655 | h1655
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1656 | h1656
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1657 | h1657
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1658 | h1658
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1659 | h1659
                              · linarith only [h1649, h1652, h1657, h1659, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1649, h1659, hc03, hc34, hlam, hphi, p0_1]
                            · linarith only [h1649, h1653, h1657, h1658, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1646, h1653, h1657, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1646, h1653, h1656, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1646, h1652, h1653, h1655, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1646, h1652, h1653, h1654, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1646, h1652, h1653, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1645, h1652, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1645, h1651, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1650, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1671 | h1671
            · rcases p0_3 (m.d 0 6) (by simp) with h1672 | h1672
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1673 | h1673
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1674 | h1674
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1675 | h1675
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1676 | h1676
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1677 | h1677
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1678 | h1678
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1679 | h1679
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1680 | h1680
                              · linarith only [h1672, h1673, h1679, h1680, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1649, h1680, hlam]
                            · linarith only [h1646, h1674, h1679, hc13, hc26, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1646, h1674, h1678, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1646, h1674, h1677, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1646, h1673, h1674, h1676, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1646, h1673, h1674, h1675, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1646, h1673, h1674, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1645, h1673, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1645, h1672, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1671, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1692 | h1692
        · linarith only [h1692, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1694 | h1694
          · rcases p0_3 (m.d 0 5) (by simp) with h1695 | h1695
            · rcases p0_3 (m.d 0 6) (by simp) with h1696 | h1696
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1697 | h1697
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1698 | h1698
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1699 | h1699
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1700 | h1700
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1701 | h1701
                        · linarith only [h1646, h1701, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1703 | h1703
                          · linarith only [h1694, h1699, h1701, h1703, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1694, h1697, h1701, h1703, hc12, hc24, hlam, hphi, p0_1]
                      · linarith only [h1694, h1699, h1700, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1645, h1646, h1697, h1699, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1645, h1646, h1697, h1698, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1645, h1646, h1697, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1645, h1696, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1695, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1712 | h1712
            · rcases p0_3 (m.d 0 6) (by simp) with h1713 | h1713
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1714 | h1714
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1715 | h1715
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1716 | h1716
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1717 | h1717
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1718 | h1718
                        · linarith only [h1646, h1718, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1720 | h1720
                          · linarith only [h1713, h1717, h1718, h1720, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1722 | h1722
                            · linarith only [h1713, h1717, h1718, h1722, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                            · linarith only [h1713, h1718, h1722, hc02, hc26, hlam, hphi, p0_1]
                      · linarith only [h1645, h1717, hc03, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1645, h1646, h1714, h1716, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1645, h1646, h1714, h1715, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1645, h1646, h1714, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1645, h1713, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1712, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1731 | h1731
      · rcases p0_3 (m.d 0 3) (by simp) with h1732 | h1732
        · linarith only [h1732, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1734 | h1734
          · rcases p0_3 (m.d 0 5) (by simp) with h1735 | h1735
            · rcases p0_3 (m.d 0 6) (by simp) with h1736 | h1736
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1737 | h1737
                · linarith only [h1645, h1737, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1645, h1731, h1737, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1731, h1736, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1735, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1742 | h1742
            · rcases p0_3 (m.d 0 6) (by simp) with h1743 | h1743
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1744 | h1744
                · linarith only [h1645, h1731, h1744, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1645, h1731, h1744, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1731, h1743, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1742, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1749 | h1749
        · linarith only [h1749, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1751 | h1751
          · rcases p0_3 (m.d 0 5) (by simp) with h1752 | h1752
            · rcases p0_3 (m.d 0 6) (by simp) with h1753 | h1753
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1754 | h1754
                · linarith only [h1645, h1754, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1756 | h1756
                  · linarith only [h1645, h1756, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1758 | h1758
                    · linarith only [h1731, h1754, h1758, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1731, h1751, h1754, h1758, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h1753, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1752, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1763 | h1763
            · rcases p0_3 (m.d 0 6) (by simp) with h1764 | h1764
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1765 | h1765
                · linarith only [h1645, h1765, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1767 | h1767
                  · linarith only [h1645, h1767, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1769 | h1769
                    · linarith only [h1731, h1765, h1769, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1771 | h1771
                      · linarith only [h1731, h1765, h1771, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h1731, h1764, h1765, h1771, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h1764, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1763, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1776 | h1776
    · rcases p0_3 (m.d 0 2) (by simp) with h1777 | h1777
      · rcases p0_3 (m.d 0 3) (by simp) with h1778 | h1778
        · rcases p0_3 (m.d 0 4) (by simp) with h1779 | h1779
          · linarith only [h1779, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1781 | h1781
            · rcases p0_3 (m.d 0 6) (by simp) with h1782 | h1782
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1783 | h1783
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1784 | h1784
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1785 | h1785
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1786 | h1786
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1787 | h1787
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1788 | h1788
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1789 | h1789
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1790 | h1790
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h1791 | h1791
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h1792 | h1792
                                  · linarith only [h1792, hlam, p0_0]
                                  · linarith only [h1785, h1792, hc14, hc45, hlam, hphi, p0_1]
                                · linarith only [h1778, h1785, h1791, hc14, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                              · linarith only [h1778, h1785, h1790, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                            · linarith only [h1778, h1785, h1787, h1789, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1778, h1785, h1787, h1788, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1777, h1785, h1787, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1777, h1783, h1785, h1786, hc14, hc16, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1777, h1783, h1785, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1777, h1783, h1784, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1776, h1783, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1776, h1782, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1781, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1806 | h1806
          · linarith only [h1806, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1808 | h1808
            · rcases p0_3 (m.d 0 6) (by simp) with h1809 | h1809
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1810 | h1810
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1811 | h1811
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1812 | h1812
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1813 | h1813
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1814 | h1814
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1815 | h1815
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1816 | h1816
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h1817 | h1817
                              · linarith only [h1778, h1817, hlam]
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h1819 | h1819
                                · linarith only [h1809, h1810, h1816, h1817, h1819, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi3]
                                · linarith only [h1809, h1811, h1817, h1819, hc13, hc36, hlam, hphi, p0_1]
                            · linarith only [h1777, h1812, h1816, hc14, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                          · linarith only [h1777, h1778, h1811, h1815, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1777, h1778, h1811, h1814, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h1777, h1778, h1810, h1811, h1813, hc13, hc16, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1777, h1778, h1810, h1811, h1812, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1777, h1778, h1810, h1811, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1776, h1778, h1810, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1776, h1809, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1808, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1831 | h1831
        · rcases p0_3 (m.d 0 4) (by simp) with h1832 | h1832
          · linarith only [h1832, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1834 | h1834
            · rcases p0_3 (m.d 0 6) (by simp) with h1835 | h1835
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1836 | h1836
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1837 | h1837
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1838 | h1838
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1839 | h1839
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1840 | h1840
                        · linarith only [h1777, h1831, h1837, h1840, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h1777, h1831, h1836, h1840, hc12, hc23, hlam, hphi, p0_1]
                      · linarith only [h1777, h1831, h1836, h1837, h1839, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1777, h1831, h1836, h1837, h1838, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1776, h1777, h1836, h1837, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1776, h1777, h1836, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1776, h1835, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1834, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1849 | h1849
          · linarith only [h1849, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1851 | h1851
            · rcases p0_3 (m.d 0 6) (by simp) with h1852 | h1852
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1853 | h1853
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1854 | h1854
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1855 | h1855
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1856 | h1856
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1857 | h1857
                        · linarith only [h1777, h1852, h1856, h1857, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h1859 | h1859
                          · linarith only [h1777, h1859, hlam]
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h1861 | h1861
                            · linarith only [h1831, h1852, h1856, h1857, h1861, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                            · linarith only [h1831, h1852, h1857, h1861, hc02, hc26, hlam, hphi, p0_1]
                      · linarith only [h1776, h1777, h1853, h1856, hc12, hc16, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                    · linarith only [h1776, h1777, h1853, h1855, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1776, h1777, h1853, h1854, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1776, h1777, h1853, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1776, h1852, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1851, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1870 | h1870
      · rcases p0_3 (m.d 0 3) (by simp) with h1871 | h1871
        · rcases p0_3 (m.d 0 4) (by simp) with h1872 | h1872
          · linarith only [h1872, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1874 | h1874
            · rcases p0_3 (m.d 0 6) (by simp) with h1875 | h1875
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1876 | h1876
                · linarith only [h1776, h1876, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1776, h1870, h1876, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1870, h1875, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1874, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1881 | h1881
          · linarith only [h1881, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1883 | h1883
            · rcases p0_3 (m.d 0 6) (by simp) with h1884 | h1884
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1885 | h1885
                · linarith only [h1776, h1870, h1885, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1776, h1870, h1885, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1870, h1884, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1883, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1890 | h1890
        · rcases p0_3 (m.d 0 4) (by simp) with h1891 | h1891
          · linarith only [h1891, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1893 | h1893
            · rcases p0_3 (m.d 0 6) (by simp) with h1894 | h1894
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1895 | h1895
                · linarith only [h1776, h1895, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1897 | h1897
                  · linarith only [h1870, h1895, h1897, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1870, h1890, h1895, h1897, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h1894, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1893, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1902 | h1902
          · linarith only [h1902, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1904 | h1904
            · rcases p0_3 (m.d 0 6) (by simp) with h1905 | h1905
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1906 | h1906
                · linarith only [h1776, h1906, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1908 | h1908
                  · linarith only [h1870, h1906, h1908, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1910 | h1910
                    · linarith only [h1776, h1910, hlam]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h1912 | h1912
                      · linarith only [h1870, h1906, h1912, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h1870, h1905, h1906, h1912, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h1905, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
            · linarith only [h1904, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1919 | h1919
    · linarith only [h1919, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h1921 | h1921
      · rcases p0_3 (m.d 0 3) (by simp) with h1922 | h1922
        · rcases p0_3 (m.d 0 4) (by simp) with h1923 | h1923
          · rcases p0_3 (m.d 0 5) (by simp) with h1924 | h1924
            · rcases p0_3 (m.d 0 6) (by simp) with h1925 | h1925
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1926 | h1926
                · linarith only [h1921, h1926, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1926, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1925, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1930 | h1930
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1931 | h1931
                · linarith only [h1921, h1931, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1931, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1930, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1935 | h1935
            · rcases p0_3 (m.d 0 6) (by simp) with h1936 | h1936
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1937 | h1937
                · linarith only [h1921, h1937, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1937, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1936, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1941 | h1941
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1942 | h1942
                · linarith only [h1921, h1942, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1942, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1941, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1946 | h1946
          · rcases p0_3 (m.d 0 5) (by simp) with h1947 | h1947
            · rcases p0_3 (m.d 0 6) (by simp) with h1948 | h1948
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1949 | h1949
                · linarith only [h1921, h1949, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1949, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1948, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1953 | h1953
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1954 | h1954
                · linarith only [h1921, h1954, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1954, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1953, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1958 | h1958
            · rcases p0_3 (m.d 0 6) (by simp) with h1959 | h1959
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1960 | h1960
                · linarith only [h1921, h1960, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1960, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1959, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1964 | h1964
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1965 | h1965
                · linarith only [h1921, h1965, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1965, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h1964, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1969 | h1969
        · rcases p0_3 (m.d 0 4) (by simp) with h1970 | h1970
          · rcases p0_3 (m.d 0 5) (by simp) with h1971 | h1971
            · rcases p0_3 (m.d 0 6) (by simp) with h1972 | h1972
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1973 | h1973
                · linarith only [h1969, h1973, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1973, hlam]
              · linarith only [h1972, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1977 | h1977
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1978 | h1978
                · linarith only [h1969, h1978, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1978, hlam]
              · linarith only [h1977, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1982 | h1982
            · rcases p0_3 (m.d 0 6) (by simp) with h1983 | h1983
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1984 | h1984
                · linarith only [h1969, h1984, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1984, hlam]
              · linarith only [h1983, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1988 | h1988
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1989 | h1989
                · linarith only [h1969, h1989, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1989, hlam]
              · linarith only [h1988, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1993 | h1993
          · rcases p0_3 (m.d 0 5) (by simp) with h1994 | h1994
            · rcases p0_3 (m.d 0 6) (by simp) with h1995 | h1995
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1996 | h1996
                · linarith only [h1993, h1996, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h1996, hlam]
              · linarith only [h1995, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2000 | h2000
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2001 | h2001
                · linarith only [h1993, h2001, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h2001, hlam]
              · linarith only [h2000, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2005 | h2005
            · rcases p0_3 (m.d 0 6) (by simp) with h2006 | h2006
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2007 | h2007
                · linarith only [h2005, h2007, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h2007, hlam]
              · linarith only [h2006, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2011 | h2011
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2012 | h2012
                · linarith only [h2012, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1921, h2012, hlam]
              · linarith only [h2011, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2016 | h2016
    · rcases p0_3 (m.d 0 2) (by simp) with h2017 | h2017
      · linarith only [h2017, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2019 | h2019
        · rcases p0_3 (m.d 0 4) (by simp) with h2020 | h2020
          · rcases p0_3 (m.d 0 5) (by simp) with h2021 | h2021
            · rcases p0_3 (m.d 0 6) (by simp) with h2022 | h2022
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2023 | h2023
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2024 | h2024
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2025 | h2025
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2026 | h2026
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2027 | h2027
                        · linarith only [h2019, h2024, h2027, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2027, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h2016, h2026, hlam]
                    · linarith only [h2016, h2023, h2025, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2023, h2024, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2023, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2022, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2035 | h2035
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2036 | h2036
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2037 | h2037
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2038 | h2038
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2039 | h2039
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2040 | h2040
                        · linarith only [h2019, h2037, h2040, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2040, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h2016, h2039, hlam]
                    · linarith only [h2016, h2036, h2038, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2036, h2037, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2036, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2035, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2048 | h2048
            · rcases p0_3 (m.d 0 6) (by simp) with h2049 | h2049
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2050 | h2050
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2051 | h2051
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2052 | h2052
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2053 | h2053
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2054 | h2054
                        · linarith only [h2019, h2051, h2054, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2054, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h2016, h2053, hlam]
                    · linarith only [h2019, h2050, h2051, h2052, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2050, h2051, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2050, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2049, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2062 | h2062
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2063 | h2063
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2064 | h2064
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2065 | h2065
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2066 | h2066
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2067 | h2067
                        · linarith only [h2019, h2064, h2067, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2067, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h2016, h2066, hlam]
                    · linarith only [h2019, h2063, h2064, h2065, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2063, h2064, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2063, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2062, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2075 | h2075
          · rcases p0_3 (m.d 0 5) (by simp) with h2076 | h2076
            · rcases p0_3 (m.d 0 6) (by simp) with h2077 | h2077
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2078 | h2078
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2079 | h2079
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2080 | h2080
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2081 | h2081
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2082 | h2082
                        · linarith only [h2075, h2080, h2082, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2082, hlam]
                      · linarith only [h2016, h2081, hlam]
                    · linarith only [h2016, h2080, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2078, h2079, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2078, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2077, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2090 | h2090
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2091 | h2091
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2092 | h2092
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2093 | h2093
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2094 | h2094
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2095 | h2095
                        · linarith only [h2075, h2093, h2095, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2095, hlam]
                      · linarith only [h2016, h2094, hlam]
                    · linarith only [h2016, h2093, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2091, h2092, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2091, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2090, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2103 | h2103
            · rcases p0_3 (m.d 0 6) (by simp) with h2104 | h2104
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2105 | h2105
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2106 | h2106
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2107 | h2107
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2108 | h2108
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2109 | h2109
                        · linarith only [h2108, h2109, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2109, hlam]
                      · linarith only [h2016, h2108, hlam]
                    · linarith only [h2016, h2107, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2105, h2106, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2105, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2104, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2117 | h2117
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2118 | h2118
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2119 | h2119
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2120 | h2120
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2121 | h2121
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2122 | h2122
                        · linarith only [h2121, h2122, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2019, h2122, hlam]
                      · linarith only [h2016, h2121, hlam]
                    · linarith only [h2016, h2120, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2016, h2118, h2119, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2016, h2118, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2117, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2130 | h2130
      · linarith only [h2130, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2132 | h2132
        · rcases p0_3 (m.d 0 4) (by simp) with h2133 | h2133
          · rcases p0_3 (m.d 0 5) (by simp) with h2134 | h2134
            · rcases p0_3 (m.d 0 6) (by simp) with h2135 | h2135
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2136 | h2136
                · linarith only [h2016, h2136, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2138 | h2138
                  · linarith only [h2132, h2136, h2138, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2132, h2136, h2138, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2135, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2142 | h2142
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2143 | h2143
                · linarith only [h2016, h2143, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2145 | h2145
                  · linarith only [h2132, h2143, h2145, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2132, h2143, h2145, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2142, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2149 | h2149
            · rcases p0_3 (m.d 0 6) (by simp) with h2150 | h2150
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2151 | h2151
                · linarith only [h2016, h2151, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2153 | h2153
                  · linarith only [h2132, h2151, h2153, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2132, h2151, h2153, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2150, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2157 | h2157
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2158 | h2158
                · linarith only [h2016, h2158, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2160 | h2160
                  · linarith only [h2132, h2158, h2160, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2132, h2158, h2160, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2157, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2164 | h2164
          · rcases p0_3 (m.d 0 5) (by simp) with h2165 | h2165
            · rcases p0_3 (m.d 0 6) (by simp) with h2166 | h2166
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2167 | h2167
                · linarith only [h2016, h2167, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2169 | h2169
                  · linarith only [h2164, h2167, h2169, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2171 | h2171
                    · linarith only [h2164, h2167, h2171, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2164, h2167, h2171, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2166, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2175 | h2175
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2176 | h2176
                · linarith only [h2016, h2176, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2178 | h2178
                  · linarith only [h2164, h2176, h2178, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2180 | h2180
                    · linarith only [h2164, h2176, h2180, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2164, h2176, h2180, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2175, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2184 | h2184
            · rcases p0_3 (m.d 0 6) (by simp) with h2185 | h2185
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2186 | h2186
                · linarith only [h2016, h2186, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2188 | h2188
                  · linarith only [h2184, h2186, h2188, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2190 | h2190
                    · linarith only [h2184, h2186, h2190, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2192 | h2192
                      · linarith only [h2184, h2186, h2192, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h2186, h2192, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2185, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2196 | h2196
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2197 | h2197
                · linarith only [h2016, h2197, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2199 | h2199
                  · linarith only [h2197, h2199, hc06, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2201 | h2201
                    · linarith only [h2197, h2201, hc06, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2203 | h2203
                      · linarith only [h2197, h2203, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h2197, h2203, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2196, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2207 | h2207
    · rcases p0_3 (m.d 0 2) (by simp) with h2208 | h2208
      · rcases p0_3 (m.d 0 3) (by simp) with h2209 | h2209
        · linarith only [h2209, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2211 | h2211
          · rcases p0_3 (m.d 0 5) (by simp) with h2212 | h2212
            · rcases p0_3 (m.d 0 6) (by simp) with h2213 | h2213
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2214 | h2214
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2215 | h2215
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2216 | h2216
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2217 | h2217
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2218 | h2218
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2219 | h2219
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2220 | h2220
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2221 | h2221
                              · linarith only [h2211, h2214, h2219, h2221, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2211, h2221, hc03, hc34, hlam, hphi, p0_1]
                            · linarith only [h2208, h2220, hlam]
                          · linarith only [h2208, h2218, h2219, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2208, h2215, h2218, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2207, h2217, hlam]
                    · linarith only [h2207, h2215, h2216, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2208, h2214, h2215, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2214, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2213, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2232 | h2232
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2233 | h2233
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2234 | h2234
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2235 | h2235
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2236 | h2236
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2237 | h2237
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2238 | h2238
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2239 | h2239
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2240 | h2240
                              · linarith only [h2211, h2233, h2238, h2240, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2211, h2240, hc03, hc34, hlam, hphi, p0_1]
                            · linarith only [h2208, h2239, hlam]
                          · linarith only [h2208, h2237, h2238, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2208, h2234, h2237, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2207, h2236, hlam]
                    · linarith only [h2207, h2234, h2235, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2208, h2233, h2234, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2233, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2232, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2251 | h2251
            · rcases p0_3 (m.d 0 6) (by simp) with h2252 | h2252
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2253 | h2253
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2254 | h2254
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2255 | h2255
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2256 | h2256
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2257 | h2257
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2258 | h2258
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2259 | h2259
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2260 | h2260
                              · linarith only [h2253, h2259, h2260, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2211, h2260, hlam]
                            · linarith only [h2208, h2259, hlam]
                          · linarith only [h2208, h2258, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2208, h2254, h2257, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2207, h2256, hlam]
                    · linarith only [h2207, h2254, h2255, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2208, h2253, h2254, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2253, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2252, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2271 | h2271
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2272 | h2272
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2273 | h2273
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2274 | h2274
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2275 | h2275
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2276 | h2276
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2277 | h2277
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2278 | h2278
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2279 | h2279
                              · linarith only [h2272, h2278, h2279, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2211, h2279, hlam]
                            · linarith only [h2208, h2278, hlam]
                          · linarith only [h2208, h2277, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2208, h2273, h2276, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2207, h2275, hlam]
                    · linarith only [h2207, h2273, h2274, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2208, h2272, h2273, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2272, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2271, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2290 | h2290
        · linarith only [h2290, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2292 | h2292
          · rcases p0_3 (m.d 0 5) (by simp) with h2293 | h2293
            · rcases p0_3 (m.d 0 6) (by simp) with h2294 | h2294
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2295 | h2295
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2296 | h2296
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2297 | h2297
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2298 | h2298
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2299 | h2299
                        · linarith only [h2208, h2299, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2301 | h2301
                          · linarith only [h2292, h2297, h2299, h2301, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2292, h2299, h2301, hc02, hc24, hlam, hphi, p0_1]
                      · linarith only [h2207, h2298, hlam]
                    · linarith only [h2207, h2208, h2295, h2297, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2207, h2208, h2295, h2296, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2208, h2295, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2294, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2309 | h2309
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2310 | h2310
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2311 | h2311
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2312 | h2312
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2313 | h2313
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2314 | h2314
                        · linarith only [h2208, h2314, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2316 | h2316
                          · linarith only [h2292, h2312, h2314, h2316, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2292, h2314, h2316, hc02, hc24, hlam, hphi, p0_1]
                      · linarith only [h2207, h2313, hlam]
                    · linarith only [h2207, h2208, h2310, h2312, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2207, h2208, h2310, h2311, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2208, h2310, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2309, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2324 | h2324
            · rcases p0_3 (m.d 0 6) (by simp) with h2325 | h2325
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2326 | h2326
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2327 | h2327
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2328 | h2328
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2329 | h2329
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2330 | h2330
                        · linarith only [h2208, h2330, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2332 | h2332
                          · linarith only [h2329, h2330, h2332, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2334 | h2334
                            · linarith only [h2329, h2330, h2334, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                            · linarith only [h2330, h2334, hc02, hc26, hlam, hphi, p0_1]
                      · linarith only [h2207, h2329, hlam]
                    · linarith only [h2207, h2208, h2326, h2328, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2207, h2208, h2326, h2327, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2208, h2326, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2325, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2342 | h2342
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2343 | h2343
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2344 | h2344
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2345 | h2345
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2346 | h2346
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2347 | h2347
                        · linarith only [h2208, h2347, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2349 | h2349
                          · linarith only [h2346, h2347, h2349, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2351 | h2351
                            · linarith only [h2346, h2347, h2351, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                            · linarith only [h2347, h2351, hc02, hc26, hlam, hphi, p0_1]
                      · linarith only [h2207, h2346, hlam]
                    · linarith only [h2207, h2208, h2343, h2345, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2207, h2208, h2343, h2344, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2208, h2343, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2342, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2359 | h2359
      · rcases p0_3 (m.d 0 3) (by simp) with h2360 | h2360
        · linarith only [h2360, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2362 | h2362
          · rcases p0_3 (m.d 0 5) (by simp) with h2363 | h2363
            · rcases p0_3 (m.d 0 6) (by simp) with h2364 | h2364
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2365 | h2365
                · linarith only [h2207, h2359, h2365, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2359, h2365, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2364, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2369 | h2369
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2370 | h2370
                · linarith only [h2207, h2359, h2370, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2359, h2370, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2369, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2374 | h2374
            · rcases p0_3 (m.d 0 6) (by simp) with h2375 | h2375
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2376 | h2376
                · linarith only [h2207, h2359, h2376, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2359, h2376, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2375, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2380 | h2380
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2381 | h2381
                · linarith only [h2207, h2359, h2381, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2207, h2359, h2381, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2380, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2385 | h2385
        · linarith only [h2385, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2387 | h2387
          · rcases p0_3 (m.d 0 5) (by simp) with h2388 | h2388
            · rcases p0_3 (m.d 0 6) (by simp) with h2389 | h2389
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2390 | h2390
                · linarith only [h2207, h2387, h2390, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2392 | h2392
                  · linarith only [h2207, h2392, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2394 | h2394
                    · linarith only [h2359, h2387, h2390, h2394, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2359, h2387, h2390, h2394, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2389, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2398 | h2398
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2399 | h2399
                · linarith only [h2207, h2387, h2399, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2401 | h2401
                  · linarith only [h2207, h2401, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2403 | h2403
                    · linarith only [h2359, h2387, h2399, h2403, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2359, h2387, h2399, h2403, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2398, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2407 | h2407
            · rcases p0_3 (m.d 0 6) (by simp) with h2408 | h2408
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2409 | h2409
                · linarith only [h2207, h2407, h2409, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2411 | h2411
                  · linarith only [h2207, h2411, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2413 | h2413
                    · linarith only [h2359, h2407, h2409, h2413, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2415 | h2415
                      · linarith only [h2359, h2407, h2409, h2415, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h2359, h2409, h2415, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2408, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2419 | h2419
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2420 | h2420
                · linarith only [h2207, h2420, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2422 | h2422
                  · linarith only [h2207, h2422, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2424 | h2424
                    · linarith only [h2359, h2420, h2424, hc06, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2426 | h2426
                      · linarith only [h2359, h2420, h2426, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h2359, h2420, h2426, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2419, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2430 | h2430
    · rcases p0_3 (m.d 0 2) (by simp) with h2431 | h2431
      · rcases p0_3 (m.d 0 3) (by simp) with h2432 | h2432
        · rcases p0_3 (m.d 0 4) (by simp) with h2433 | h2433
          · linarith only [h2433, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2435 | h2435
            · rcases p0_3 (m.d 0 6) (by simp) with h2436 | h2436
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2437 | h2437
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2438 | h2438
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2439 | h2439
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2440 | h2440
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2441 | h2441
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2442 | h2442
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2443 | h2443
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2444 | h2444
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h2445 | h2445
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h2446 | h2446
                                  · linarith only [h2437, h2441, h2445, h2446, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                  · linarith only [h2435, h2446, hc04, hc45, hlam, hphi, p0_1]
                                · linarith only [h2432, h2445, hlam]
                              · linarith only [h2432, h2439, h2444, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2431, h2443, hlam]
                          · linarith only [h2431, h2439, h2442, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2431, h2439, h2441, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2430, h2440, hlam]
                    · linarith only [h2430, h2439, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2431, h2437, h2438, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2437, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h2436, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2459 | h2459
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2460 | h2460
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2461 | h2461
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2462 | h2462
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2463 | h2463
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2464 | h2464
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2465 | h2465
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2466 | h2466
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2467 | h2467
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h2468 | h2468
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h2469 | h2469
                                  · linarith only [h2460, h2464, h2468, h2469, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                  · linarith only [h2435, h2469, hlam]
                                · linarith only [h2432, h2468, hlam]
                              · linarith only [h2432, h2467, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b, p0_1]
                            · linarith only [h2431, h2466, hlam]
                          · linarith only [h2431, h2462, h2465, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2431, h2462, h2464, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2430, h2463, hlam]
                    · linarith only [h2430, h2462, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2431, h2460, h2461, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2460, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h2459, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2482 | h2482
          · linarith only [h2482, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2484 | h2484
            · rcases p0_3 (m.d 0 6) (by simp) with h2485 | h2485
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2486 | h2486
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2487 | h2487
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2488 | h2488
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2489 | h2489
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2490 | h2490
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2491 | h2491
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2492 | h2492
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2493 | h2493
                              · linarith only [h2432, h2493, hlam]
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h2495 | h2495
                                · linarith only [h2486, h2492, h2493, h2495, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi3]
                                · linarith only [h2493, h2495, hc03, hc36, hlam, hphi, p0_1]
                            · linarith only [h2431, h2492, hlam]
                          · linarith only [h2431, h2491, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2431, h2432, h2487, h2490, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2430, h2489, hlam]
                    · linarith only [h2430, h2432, h2487, h2488, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2431, h2432, h2486, h2487, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2432, h2486, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2485, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2506 | h2506
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2507 | h2507
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2508 | h2508
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2509 | h2509
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2510 | h2510
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2511 | h2511
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2512 | h2512
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2513 | h2513
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2514 | h2514
                              · linarith only [h2432, h2514, hlam]
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h2516 | h2516
                                · linarith only [h2507, h2513, h2514, h2516, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi3]
                                · linarith only [h2514, h2516, hc03, hc36, hlam, hphi, p0_1]
                            · linarith only [h2431, h2513, hlam]
                          · linarith only [h2431, h2512, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2431, h2432, h2508, h2511, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2430, h2510, hlam]
                    · linarith only [h2430, h2432, h2508, h2509, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2431, h2432, h2507, h2508, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2432, h2507, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2506, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2527 | h2527
        · rcases p0_3 (m.d 0 4) (by simp) with h2528 | h2528
          · linarith only [h2528, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2530 | h2530
            · rcases p0_3 (m.d 0 6) (by simp) with h2531 | h2531
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2532 | h2532
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2533 | h2533
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2534 | h2534
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2535 | h2535
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2536 | h2536
                        · linarith only [h2431, h2527, h2533, h2536, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2431, h2527, h2532, h2536, hc12, hc23, hlam, hphi, p0_1]
                      · linarith only [h2430, h2535, hlam]
                    · linarith only [h2431, h2527, h2532, h2533, h2534, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2430, h2431, h2532, h2533, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2431, h2532, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2531, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2544 | h2544
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2545 | h2545
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2546 | h2546
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2547 | h2547
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2548 | h2548
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2549 | h2549
                        · linarith only [h2431, h2527, h2546, h2549, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2431, h2527, h2549, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h2430, h2548, hlam]
                    · linarith only [h2431, h2527, h2545, h2546, h2547, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2430, h2431, h2545, h2546, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2431, h2545, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2544, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2557 | h2557
          · linarith only [h2557, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2559 | h2559
            · rcases p0_3 (m.d 0 6) (by simp) with h2560 | h2560
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2561 | h2561
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2562 | h2562
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2563 | h2563
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2564 | h2564
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2565 | h2565
                        · linarith only [h2431, h2564, h2565, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2567 | h2567
                          · linarith only [h2431, h2567, hlam]
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2569 | h2569
                            · linarith only [h2527, h2564, h2565, h2569, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                            · linarith only [h2527, h2565, h2569, hc02, hc26, hlam, hphi, p0_1]
                      · linarith only [h2430, h2564, hlam]
                    · linarith only [h2430, h2527, h2563, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2430, h2431, h2561, h2562, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2431, h2561, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2560, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2577 | h2577
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2578 | h2578
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2579 | h2579
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2580 | h2580
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2581 | h2581
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2582 | h2582
                        · linarith only [h2431, h2581, h2582, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2584 | h2584
                          · linarith only [h2431, h2584, hlam]
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2586 | h2586
                            · linarith only [h2527, h2581, h2582, h2586, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                            · linarith only [h2527, h2582, h2586, hc02, hc26, hlam, hphi, p0_1]
                      · linarith only [h2430, h2581, hlam]
                    · linarith only [h2430, h2431, h2578, h2580, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2430, h2431, h2578, h2579, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2431, h2578, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2577, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2594 | h2594
      · rcases p0_3 (m.d 0 3) (by simp) with h2595 | h2595
        · rcases p0_3 (m.d 0 4) (by simp) with h2596 | h2596
          · linarith only [h2596, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2598 | h2598
            · rcases p0_3 (m.d 0 6) (by simp) with h2599 | h2599
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2600 | h2600
                · linarith only [h2430, h2594, h2600, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2594, h2600, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2599, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2604 | h2604
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2605 | h2605
                · linarith only [h2430, h2594, h2605, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2594, h2605, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2604, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2609 | h2609
          · linarith only [h2609, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2611 | h2611
            · rcases p0_3 (m.d 0 6) (by simp) with h2612 | h2612
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2613 | h2613
                · linarith only [h2430, h2594, h2613, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2594, h2613, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2612, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2617 | h2617
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2618 | h2618
                · linarith only [h2430, h2594, h2618, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2430, h2594, h2618, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2617, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2622 | h2622
        · rcases p0_3 (m.d 0 4) (by simp) with h2623 | h2623
          · linarith only [h2623, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2625 | h2625
            · rcases p0_3 (m.d 0 6) (by simp) with h2626 | h2626
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2627 | h2627
                · linarith only [h2430, h2622, h2627, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2629 | h2629
                  · linarith only [h2594, h2622, h2627, h2629, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2594, h2622, h2627, h2629, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2626, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2633 | h2633
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2634 | h2634
                · linarith only [h2430, h2622, h2634, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2636 | h2636
                  · linarith only [h2594, h2622, h2634, h2636, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2594, h2622, h2634, h2636, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2633, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2640 | h2640
          · linarith only [h2640, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2642 | h2642
            · rcases p0_3 (m.d 0 6) (by simp) with h2643 | h2643
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2644 | h2644
                · linarith only [h2430, h2642, h2644, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2646 | h2646
                  · linarith only [h2594, h2642, h2644, h2646, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2648 | h2648
                    · linarith only [h2430, h2648, hlam]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2650 | h2650
                      · linarith only [h2594, h2642, h2644, h2650, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h2594, h2644, h2650, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2643, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2654 | h2654
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2655 | h2655
                · linarith only [h2430, h2655, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2657 | h2657
                  · linarith only [h2594, h2655, h2657, hc06, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2659 | h2659
                    · linarith only [h2430, h2659, hlam]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2661 | h2661
                      · linarith only [h2594, h2655, h2661, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h2594, h2655, h2661, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2654, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2665 | h2665
    · rcases p0_3 (m.d 0 2) (by simp) with h2666 | h2666
      · rcases p0_3 (m.d 0 3) (by simp) with h2667 | h2667
        · rcases p0_3 (m.d 0 4) (by simp) with h2668 | h2668
          · rcases p0_3 (m.d 0 5) (by simp) with h2669 | h2669
            · linarith only [h2669, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2671 | h2671
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2672 | h2672
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2673 | h2673
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2674 | h2674
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2675 | h2675
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2676 | h2676
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2677 | h2677
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2678 | h2678
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2679 | h2679
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h2680 | h2680
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h2681 | h2681
                                  · rcases m.htr 0 4 6 (by decide) (by decide) with h2682 | h2682
                                    · rcases m.htr 0 5 6 (by decide) (by decide) with h2683 | h2683
                                      · linarith only [h2683, hlam, p0_0]
                                      · linarith only [h2683, hc05, hc56, hlam, hphi, p0_1]
                                    · linarith only [h2668, h2682, hlam]
                                  · linarith only [h2668, h2681, hc05, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, p0_1]
                                · linarith only [h2667, h2680, hlam]
                              · linarith only [h2667, h2679, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                            · linarith only [h2666, h2678, hlam]
                          · linarith only [h2666, h2677, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                        · linarith only [h2666, h2676, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, p0_1]
                      · linarith only [h2665, h2675, hlam]
                    · linarith only [h2665, h2674, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h2666, h2672, h2673, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h2665, h2672, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h2671, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2698 | h2698
            · linarith only [h2698, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2700 | h2700
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2701 | h2701
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2702 | h2702
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2703 | h2703
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2704 | h2704
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2705 | h2705
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2706 | h2706
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2707 | h2707
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2708 | h2708
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h2709 | h2709
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h2710 | h2710
                                  · linarith only [h2668, h2710, hlam]
                                  · rcases m.htr 0 4 6 (by decide) (by decide) with h2712 | h2712
                                    · linarith only [h2701, h2705, h2709, h2710, h2712, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi4]
                                    · linarith only [h2710, h2712, hc04, hc46, hlam, hphi, p0_1]
                                · linarith only [h2667, h2709, hlam]
                              · linarith only [h2667, h2708, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, p0_1]
                            · linarith only [h2666, h2707, hlam]
                          · linarith only [h2666, h2668, h2703, h2706, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2666, h2668, h2703, h2705, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2665, h2704, hlam]
                    · linarith only [h2665, h2668, h2703, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2666, h2668, h2701, h2702, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2668, h2701, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h2700, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2725 | h2725
          · rcases p0_3 (m.d 0 5) (by simp) with h2726 | h2726
            · linarith only [h2726, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2728 | h2728
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2729 | h2729
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2730 | h2730
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2731 | h2731
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2732 | h2732
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2733 | h2733
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2734 | h2734
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2735 | h2735
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2736 | h2736
                              · linarith only [h2667, h2725, h2729, h2734, h2736, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · linarith only [h2667, h2725, h2736, hc03, hc34, hlam, hphi, p0_1]
                            · linarith only [h2666, h2735, hlam]
                          · linarith only [h2666, h2667, h2733, h2734, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2666, h2667, h2730, h2733, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2665, h2732, hlam]
                    · linarith only [h2665, h2667, h2730, h2731, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2666, h2667, h2729, h2730, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2667, h2729, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2728, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2747 | h2747
            · linarith only [h2747, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2749 | h2749
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2750 | h2750
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2751 | h2751
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2752 | h2752
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2753 | h2753
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2754 | h2754
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2755 | h2755
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2756 | h2756
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h2757 | h2757
                              · linarith only [h2667, h2750, h2756, h2757, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                              · rcases m.htr 0 3 6 (by decide) (by decide) with h2759 | h2759
                                · linarith only [h2725, h2750, h2756, h2757, h2759, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi3]
                                · linarith only [h2725, h2757, h2759, hc03, hc36, hlam, hphi, p0_1]
                            · linarith only [h2666, h2756, hlam]
                          · linarith only [h2666, h2667, h2754, h2755, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2666, h2667, h2751, h2754, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b, p0_1]
                      · linarith only [h2665, h2753, hlam]
                    · linarith only [h2665, h2667, h2751, h2752, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2666, h2667, h2750, h2751, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2667, h2750, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2749, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2770 | h2770
        · rcases p0_3 (m.d 0 4) (by simp) with h2771 | h2771
          · rcases p0_3 (m.d 0 5) (by simp) with h2772 | h2772
            · linarith only [h2772, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2774 | h2774
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2775 | h2775
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2776 | h2776
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2777 | h2777
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2778 | h2778
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2779 | h2779
                        · linarith only [h2666, h2770, h2776, h2779, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2666, h2770, h2779, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h2665, h2778, hlam]
                    · linarith only [h2665, h2666, h2775, h2777, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2665, h2666, h2775, h2776, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2666, h2775, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2774, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2787 | h2787
            · linarith only [h2787, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2789 | h2789
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2790 | h2790
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2791 | h2791
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2792 | h2792
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2793 | h2793
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2794 | h2794
                        · linarith only [h2666, h2770, h2791, h2794, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · linarith only [h2666, h2770, h2794, hc02, hc23, hlam, hphi, p0_1]
                      · linarith only [h2665, h2793, hlam]
                    · linarith only [h2666, h2770, h2790, h2791, h2792, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2665, h2666, h2790, h2791, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2666, h2790, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2789, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2802 | h2802
          · rcases p0_3 (m.d 0 5) (by simp) with h2803 | h2803
            · linarith only [h2803, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2805 | h2805
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2806 | h2806
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2807 | h2807
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2808 | h2808
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2809 | h2809
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2810 | h2810
                        · linarith only [h2666, h2802, h2808, h2810, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2812 | h2812
                          · linarith only [h2770, h2802, h2808, h2810, h2812, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · linarith only [h2770, h2802, h2810, h2812, hc02, hc24, hlam, hphi, p0_1]
                      · linarith only [h2665, h2809, hlam]
                    · linarith only [h2665, h2770, h2808, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2665, h2666, h2806, h2807, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2666, h2806, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2805, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2820 | h2820
            · linarith only [h2820, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2822 | h2822
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2823 | h2823
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2824 | h2824
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2825 | h2825
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2826 | h2826
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h2827 | h2827
                        · linarith only [h2666, h2826, h2827, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h2829 | h2829
                          · linarith only [h2770, h2826, h2827, h2829, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                          · rcases m.htr 0 2 6 (by decide) (by decide) with h2831 | h2831
                            · linarith only [h2770, h2826, h2827, h2831, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi2]
                            · linarith only [h2770, h2827, h2831, hc02, hc26, hlam, hphi, p0_1]
                      · linarith only [h2665, h2826, hlam]
                    · linarith only [h2665, h2666, h2823, h2825, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2665, h2666, h2823, h2824, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2666, h2823, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h2822, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h2839 | h2839
      · rcases p0_3 (m.d 0 3) (by simp) with h2840 | h2840
        · rcases p0_3 (m.d 0 4) (by simp) with h2841 | h2841
          · rcases p0_3 (m.d 0 5) (by simp) with h2842 | h2842
            · linarith only [h2842, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2844 | h2844
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2845 | h2845
                · linarith only [h2665, h2839, h2845, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2839, h2845, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2844, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2849 | h2849
            · linarith only [h2849, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2851 | h2851
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2852 | h2852
                · linarith only [h2665, h2839, h2852, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2839, h2852, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2851, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2856 | h2856
          · rcases p0_3 (m.d 0 5) (by simp) with h2857 | h2857
            · linarith only [h2857, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2859 | h2859
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2860 | h2860
                · linarith only [h2665, h2839, h2860, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2839, h2860, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2859, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2864 | h2864
            · linarith only [h2864, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2866 | h2866
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2867 | h2867
                · linarith only [h2665, h2839, h2867, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h2665, h2839, h2867, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h2866, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h2871 | h2871
        · rcases p0_3 (m.d 0 4) (by simp) with h2872 | h2872
          · rcases p0_3 (m.d 0 5) (by simp) with h2873 | h2873
            · linarith only [h2873, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2875 | h2875
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2876 | h2876
                · linarith only [h2665, h2871, h2876, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2878 | h2878
                  · linarith only [h2839, h2871, h2876, h2878, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2839, h2871, h2876, h2878, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2875, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2882 | h2882
            · linarith only [h2882, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2884 | h2884
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2885 | h2885
                · linarith only [h2665, h2871, h2885, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2887 | h2887
                  · linarith only [h2839, h2871, h2885, h2887, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · linarith only [h2839, h2871, h2885, h2887, hc01, hc13, hlam, hphi, p0_1]
              · linarith only [h2884, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h2891 | h2891
          · rcases p0_3 (m.d 0 5) (by simp) with h2892 | h2892
            · linarith only [h2892, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2894 | h2894
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2895 | h2895
                · linarith only [h2665, h2891, h2895, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2897 | h2897
                  · linarith only [h2839, h2891, h2895, h2897, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2899 | h2899
                    · linarith only [h2839, h2891, h2895, h2899, hc04, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · linarith only [h2839, h2891, h2895, h2899, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h2894, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h2903 | h2903
            · linarith only [h2903, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h2905 | h2905
              · rcases m.htr 0 1 2 (by decide) (by decide) with h2906 | h2906
                · linarith only [h2665, h2906, hc06, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h2908 | h2908
                  · linarith only [h2839, h2906, h2908, hc06, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h2910 | h2910
                    · linarith only [h2839, h2906, h2910, hc06, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                    · rcases m.htr 0 1 6 (by decide) (by decide) with h2912 | h2912
                      · linarith only [h2839, h2906, h2912, hc06, hlam, hphi, ht0b, ht6b, p0_1, u6ehi1]
                      · linarith only [h2839, h2906, h2912, hc01, hc16, hlam, hphi, p0_1]
              · linarith only [h2905, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
