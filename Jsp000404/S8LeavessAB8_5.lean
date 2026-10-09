import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n8l_sAB8_H_I_H_R (m : N8Model)
    (hb5 : CMSig2_8_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h5bigk := hb5.1
  have h6ehi := hb6.1
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 5) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 5) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 5 6) (by simp) with h8 | h8
              · linarith only [h8, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h8, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h11 | h11
              · linarith only [h11, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h11, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · rcases p0_3 (m.d 5 6) (by simp) with h15 | h15
              · linarith only [h15, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h15, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h18 | h18
              · linarith only [h18, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h18, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 5 6) (by simp) with h23 | h23
              · linarith only [h23, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h23, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h26 | h26
              · linarith only [h26, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h26, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · rcases p0_3 (m.d 5 6) (by simp) with h30 | h30
              · linarith only [h30, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h30, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h33 | h33
              · linarith only [h33, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h33, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
    · rcases p0_3 (m.d 1 5) (by simp) with h38 | h38
      · rcases p0_3 (m.d 2 5) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h41 | h41
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases p0_3 (m.d 5 6) (by simp) with h43 | h43
              · linarith only [h43, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h43, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h46 | h46
              · linarith only [h46, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h46, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · rcases p0_3 (m.d 5 6) (by simp) with h50 | h50
              · linarith only [h50, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h50, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h53 | h53
              · linarith only [h53, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h53, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h58 | h58
          · rcases p0_3 (m.d 4 5) (by simp) with h59 | h59
            · rcases p0_3 (m.d 5 6) (by simp) with h60 | h60
              · linarith only [h38, h60, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h60, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h63 | h63
              · linarith only [h38, h63, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h63, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · rcases p0_3 (m.d 5 6) (by simp) with h67 | h67
              · linarith only [h38, h67, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h67, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h70 | h70
              · linarith only [h38, h70, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h70, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h37, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
    · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
      · rcases p0_3 (m.d 2 5) (by simp) with h76 | h76
        · rcases p0_3 (m.d 3 5) (by simp) with h77 | h77
          · linarith only [h77, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h79 | h79
            · rcases p0_3 (m.d 5 6) (by simp) with h80 | h80
              · linarith only [h80, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h80, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h83 | h83
              · linarith only [h83, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h83, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · rcases p0_3 (m.d 5 6) (by simp) with h89 | h89
              · linarith only [h76, h89, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h89, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h92 | h92
              · linarith only [h76, h92, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h92, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 5) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · rcases p0_3 (m.d 5 6) (by simp) with h99 | h99
              · linarith only [h75, h99, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h99, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h102 | h102
              · linarith only [h102, h75, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h102, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · rcases p0_3 (m.d 5 6) (by simp) with h108 | h108
              · linarith only [h108, h75, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h108, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h111 | h111
              · linarith only [h111, h75, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h111, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h74, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h115 | h115
    · rcases p0_3 (m.d 1 5) (by simp) with h116 | h116
      · rcases p0_3 (m.d 2 5) (by simp) with h117 | h117
        · rcases p0_3 (m.d 3 5) (by simp) with h118 | h118
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h121 | h121
              · linarith only [h121, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h121, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h126 | h126
              · linarith only [h118, h126, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h126, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h129 | h129
          · rcases p0_3 (m.d 4 5) (by simp) with h130 | h130
            · linarith only [h130, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h132 | h132
              · linarith only [h117, h132, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h132, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h137 | h137
              · linarith only [h117, h137, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h137, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 5) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h144 | h144
              · linarith only [h116, h144, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h144, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h149 | h149
              · linarith only [h116, h149, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h149, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h155 | h155
              · linarith only [h116, h155, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h155, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h158 | h158
            · linarith only [h158, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h160 | h160
              · linarith only [h116, h160, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h160, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h115, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
    · linarith only [h165, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h167 | h167
      · rcases p0_3 (m.d 2 5) (by simp) with h168 | h168
        · rcases p0_3 (m.d 3 5) (by simp) with h169 | h169
          · rcases p0_3 (m.d 4 5) (by simp) with h170 | h170
            · rcases p0_3 (m.d 5 6) (by simp) with h171 | h171
              · linarith only [h171, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h171, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h174 | h174
              · linarith only [h174, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h174, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h177 | h177
            · rcases p0_3 (m.d 5 6) (by simp) with h178 | h178
              · linarith only [h178, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h178, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h181 | h181
              · linarith only [h181, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h181, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h184 | h184
          · rcases p0_3 (m.d 4 5) (by simp) with h185 | h185
            · rcases p0_3 (m.d 5 6) (by simp) with h186 | h186
              · linarith only [h186, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h186, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h189 | h189
              · linarith only [h189, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h189, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h192 | h192
            · rcases p0_3 (m.d 5 6) (by simp) with h193 | h193
              · linarith only [h193, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h193, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h196 | h196
              · linarith only [h196, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h196, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h167, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h201 | h201
    · rcases p0_3 (m.d 1 5) (by simp) with h202 | h202
      · rcases p0_3 (m.d 2 5) (by simp) with h203 | h203
        · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h205 | h205
          · rcases p0_3 (m.d 4 5) (by simp) with h206 | h206
            · rcases p0_3 (m.d 5 6) (by simp) with h207 | h207
              · linarith only [h207, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h201, h207, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h210 | h210
              · linarith only [h210, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h210, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases p0_3 (m.d 5 6) (by simp) with h214 | h214
              · linarith only [h214, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h214, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h217 | h217
              · linarith only [h217, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h217, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h202, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h221 | h221
      · rcases p0_3 (m.d 2 5) (by simp) with h222 | h222
        · linarith only [h222, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h224 | h224
          · rcases p0_3 (m.d 4 5) (by simp) with h225 | h225
            · rcases p0_3 (m.d 5 6) (by simp) with h226 | h226
              · linarith only [h201, h226, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h226, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h229 | h229
              · linarith only [h201, h229, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h229, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · rcases p0_3 (m.d 5 6) (by simp) with h233 | h233
              · linarith only [h201, h233, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h233, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h236 | h236
              · linarith only [h201, h236, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h236, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h221, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h240 | h240
    · rcases p0_3 (m.d 1 5) (by simp) with h241 | h241
      · rcases p0_3 (m.d 2 5) (by simp) with h242 | h242
        · rcases p0_3 (m.d 3 5) (by simp) with h243 | h243
          · linarith only [h243, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h245 | h245
            · rcases p0_3 (m.d 5 6) (by simp) with h246 | h246
              · linarith only [h246, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h240, h246, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h249 | h249
              · linarith only [h249, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h249, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h254 | h254
            · rcases p0_3 (m.d 5 6) (by simp) with h255 | h255
              · linarith only [h242, h255, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h255, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h258 | h258
              · linarith only [h242, h258, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h258, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h241, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h262 | h262
      · rcases p0_3 (m.d 2 5) (by simp) with h263 | h263
        · rcases p0_3 (m.d 3 5) (by simp) with h264 | h264
          · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h266 | h266
            · rcases p0_3 (m.d 5 6) (by simp) with h267 | h267
              · linarith only [h240, h267, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h267, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h270 | h270
              · linarith only [h240, h270, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h270, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h275 | h275
            · rcases p0_3 (m.d 5 6) (by simp) with h276 | h276
              · linarith only [h240, h276, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h276, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h279 | h279
              · linarith only [h240, h279, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h279, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h262, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h283 | h283
    · rcases p0_3 (m.d 1 5) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 5) (by simp) with h285 | h285
        · rcases p0_3 (m.d 3 5) (by simp) with h286 | h286
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h289 | h289
              · linarith only [h289, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h283, h289, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h292 | h292
            · linarith only [h292, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h294 | h294
              · linarith only [h286, h294, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h294, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h297 | h297
          · rcases p0_3 (m.d 4 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h300 | h300
              · linarith only [h285, h300, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h300, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h303 | h303
            · linarith only [h303, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h305 | h305
              · linarith only [h285, h305, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h305, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h284, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h309 | h309
      · rcases p0_3 (m.d 2 5) (by simp) with h310 | h310
        · rcases p0_3 (m.d 3 5) (by simp) with h311 | h311
          · rcases p0_3 (m.d 4 5) (by simp) with h312 | h312
            · linarith only [h312, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h314 | h314
              · linarith only [h283, h314, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h314, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h319 | h319
              · linarith only [h283, h319, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h319, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h322 | h322
          · rcases p0_3 (m.d 4 5) (by simp) with h323 | h323
            · linarith only [h323, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h325 | h325
              · linarith only [h283, h325, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h325, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h328 | h328
            · linarith only [h328, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h330 | h330
              · linarith only [h283, h330, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h330, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h309, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h335 | h335
    · linarith only [h335, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h337 | h337
      · rcases p0_3 (m.d 2 5) (by simp) with h338 | h338
        · rcases p0_3 (m.d 3 5) (by simp) with h339 | h339
          · rcases p0_3 (m.d 4 5) (by simp) with h340 | h340
            · rcases p0_3 (m.d 5 6) (by simp) with h341 | h341
              · linarith only [h341, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h341, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h344 | h344
              · linarith only [h344, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h344, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h347 | h347
            · rcases p0_3 (m.d 5 6) (by simp) with h348 | h348
              · linarith only [h348, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h348, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h351 | h351
              · linarith only [h351, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h351, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h338, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h355 | h355
        · rcases p0_3 (m.d 3 5) (by simp) with h356 | h356
          · rcases p0_3 (m.d 4 5) (by simp) with h357 | h357
            · rcases p0_3 (m.d 5 6) (by simp) with h358 | h358
              · linarith only [h358, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h358, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h361 | h361
              · linarith only [h361, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h361, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h364 | h364
            · rcases p0_3 (m.d 5 6) (by simp) with h365 | h365
              · linarith only [h365, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h365, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h368 | h368
              · linarith only [h368, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h368, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h355, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
    · rcases p0_3 (m.d 1 5) (by simp) with h373 | h373
      · linarith only [h373, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h375 | h375
        · rcases p0_3 (m.d 3 5) (by simp) with h376 | h376
          · rcases p0_3 (m.d 4 5) (by simp) with h377 | h377
            · rcases p0_3 (m.d 5 6) (by simp) with h378 | h378
              · linarith only [h378, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h372, h378, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h381 | h381
              · linarith only [h381, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h381, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h384 | h384
            · rcases p0_3 (m.d 5 6) (by simp) with h385 | h385
              · linarith only [h385, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h385, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h388 | h388
              · linarith only [h388, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h388, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h375, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h392 | h392
      · linarith only [h392, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h394 | h394
        · rcases p0_3 (m.d 3 5) (by simp) with h395 | h395
          · rcases p0_3 (m.d 4 5) (by simp) with h396 | h396
            · rcases p0_3 (m.d 5 6) (by simp) with h397 | h397
              · linarith only [h372, h397, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h397, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h400 | h400
              · linarith only [h372, h400, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h400, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h403 | h403
            · rcases p0_3 (m.d 5 6) (by simp) with h404 | h404
              · linarith only [h372, h404, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h404, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h407 | h407
              · linarith only [h372, h407, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h407, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h394, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h412 | h412
    · rcases p0_3 (m.d 1 5) (by simp) with h413 | h413
      · rcases p0_3 (m.d 2 5) (by simp) with h414 | h414
        · rcases p0_3 (m.d 3 5) (by simp) with h415 | h415
          · linarith only [h415, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h417 | h417
            · rcases p0_3 (m.d 5 6) (by simp) with h418 | h418
              · linarith only [h418, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h412, h418, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h421 | h421
              · linarith only [h421, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h421, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h414, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h425 | h425
        · rcases p0_3 (m.d 3 5) (by simp) with h426 | h426
          · linarith only [h426, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h428 | h428
            · rcases p0_3 (m.d 5 6) (by simp) with h429 | h429
              · linarith only [h413, h429, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h429, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h432 | h432
              · linarith only [h413, h432, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h432, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h425, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h436 | h436
      · rcases p0_3 (m.d 2 5) (by simp) with h437 | h437
        · rcases p0_3 (m.d 3 5) (by simp) with h438 | h438
          · linarith only [h438, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h440 | h440
            · rcases p0_3 (m.d 5 6) (by simp) with h441 | h441
              · linarith only [h412, h441, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h436, h441, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h444 | h444
              · linarith only [h412, h444, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h444, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h437, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h448 | h448
        · rcases p0_3 (m.d 3 5) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h451 | h451
            · rcases p0_3 (m.d 5 6) (by simp) with h452 | h452
              · linarith only [h412, h452, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h452, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h455 | h455
              · linarith only [h412, h455, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h455, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h448, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h459 | h459
    · rcases p0_3 (m.d 1 5) (by simp) with h460 | h460
      · rcases p0_3 (m.d 2 5) (by simp) with h461 | h461
        · rcases p0_3 (m.d 3 5) (by simp) with h462 | h462
          · rcases p0_3 (m.d 4 5) (by simp) with h463 | h463
            · linarith only [h463, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h465 | h465
              · linarith only [h465, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h459, h465, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · linarith only [h468, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h470 | h470
              · linarith only [h462, h470, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h470, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h474 | h474
        · rcases p0_3 (m.d 3 5) (by simp) with h475 | h475
          · rcases p0_3 (m.d 4 5) (by simp) with h476 | h476
            · linarith only [h476, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h478 | h478
              · linarith only [h460, h478, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h481 | h481
            · linarith only [h481, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h483 | h483
              · linarith only [h460, h483, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h483, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h474, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
      · rcases p0_3 (m.d 2 5) (by simp) with h488 | h488
        · rcases p0_3 (m.d 3 5) (by simp) with h489 | h489
          · rcases p0_3 (m.d 4 5) (by simp) with h490 | h490
            · linarith only [h490, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h492 | h492
              · linarith only [h459, h492, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h487, h492, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h495 | h495
            · linarith only [h495, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h497 | h497
              · linarith only [h459, h497, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h487, h497, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h501 | h501
        · rcases p0_3 (m.d 3 5) (by simp) with h502 | h502
          · rcases p0_3 (m.d 4 5) (by simp) with h503 | h503
            · linarith only [h503, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h505 | h505
              · linarith only [h459, h505, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h508 | h508
            · linarith only [h508, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h510 | h510
              · linarith only [h487, h510, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h510, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h501, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h515 | h515
    · linarith only [h515, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h517 | h517
      · rcases p0_3 (m.d 2 5) (by simp) with h518 | h518
        · rcases p0_3 (m.d 3 5) (by simp) with h519 | h519
          · rcases p0_3 (m.d 4 5) (by simp) with h520 | h520
            · rcases p0_3 (m.d 5 6) (by simp) with h521 | h521
              · linarith only [h521, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h517, h521, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h524 | h524
              · linarith only [h524, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h524, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h519, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h528 | h528
          · rcases p0_3 (m.d 4 5) (by simp) with h529 | h529
            · rcases p0_3 (m.d 5 6) (by simp) with h530 | h530
              · linarith only [h530, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h530, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h533 | h533
              · linarith only [h533, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h533, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h528, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h537 | h537
        · rcases p0_3 (m.d 3 5) (by simp) with h538 | h538
          · rcases p0_3 (m.d 4 5) (by simp) with h539 | h539
            · rcases p0_3 (m.d 5 6) (by simp) with h540 | h540
              · linarith only [h540, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h537, h540, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h543 | h543
              · linarith only [h543, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h543, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h538, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h547 | h547
          · rcases p0_3 (m.d 4 5) (by simp) with h548 | h548
            · rcases p0_3 (m.d 5 6) (by simp) with h549 | h549
              · linarith only [h549, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h549, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h552 | h552
              · linarith only [h552, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h552, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h547, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h556 | h556
    · rcases p0_3 (m.d 1 5) (by simp) with h557 | h557
      · linarith only [h557, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h559 | h559
        · rcases p0_3 (m.d 3 5) (by simp) with h560 | h560
          · rcases p0_3 (m.d 4 5) (by simp) with h561 | h561
            · rcases p0_3 (m.d 5 6) (by simp) with h562 | h562
              · linarith only [h562, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h556, h562, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h565 | h565
              · linarith only [h565, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h565, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h560, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h569 | h569
          · rcases p0_3 (m.d 4 5) (by simp) with h570 | h570
            · rcases p0_3 (m.d 5 6) (by simp) with h571 | h571
              · linarith only [h571, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h571, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h574 | h574
              · linarith only [h574, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h574, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h569, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h578 | h578
      · linarith only [h578, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h580 | h580
        · rcases p0_3 (m.d 3 5) (by simp) with h581 | h581
          · rcases p0_3 (m.d 4 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 5 6) (by simp) with h583 | h583
              · linarith only [h556, h583, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h580, h583, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h586 | h586
              · linarith only [h556, h586, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h586, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h581, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h590 | h590
          · rcases p0_3 (m.d 4 5) (by simp) with h591 | h591
            · rcases p0_3 (m.d 5 6) (by simp) with h592 | h592
              · linarith only [h556, h592, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h592, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h595 | h595
              · linarith only [h556, h595, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h595, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h590, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h599 | h599
    · rcases p0_3 (m.d 1 5) (by simp) with h600 | h600
      · rcases p0_3 (m.d 2 5) (by simp) with h601 | h601
        · linarith only [h601, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h603 | h603
          · rcases p0_3 (m.d 4 5) (by simp) with h604 | h604
            · rcases p0_3 (m.d 5 6) (by simp) with h605 | h605
              · linarith only [h605, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h599, h605, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h608 | h608
              · linarith only [h608, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h608, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h603, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h612 | h612
        · linarith only [h612, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h614 | h614
          · rcases p0_3 (m.d 4 5) (by simp) with h615 | h615
            · rcases p0_3 (m.d 5 6) (by simp) with h616 | h616
              · linarith only [h600, h616, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h616, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h619 | h619
              · linarith only [h600, h619, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h619, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h614, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h623 | h623
      · rcases p0_3 (m.d 2 5) (by simp) with h624 | h624
        · linarith only [h624, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h626 | h626
          · rcases p0_3 (m.d 4 5) (by simp) with h627 | h627
            · rcases p0_3 (m.d 5 6) (by simp) with h628 | h628
              · linarith only [h599, h628, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h623, h628, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h631 | h631
              · linarith only [h599, h631, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h631, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h626, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h635 | h635
        · linarith only [h635, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h637 | h637
          · rcases p0_3 (m.d 4 5) (by simp) with h638 | h638
            · rcases p0_3 (m.d 5 6) (by simp) with h639 | h639
              · linarith only [h599, h639, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h639, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h642 | h642
              · linarith only [h599, h642, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h642, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h637, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h647 | h647
    · rcases p0_3 (m.d 1 5) (by simp) with h648 | h648
      · rcases p0_3 (m.d 2 5) (by simp) with h649 | h649
        · rcases p0_3 (m.d 3 5) (by simp) with h650 | h650
          · rcases p0_3 (m.d 4 5) (by simp) with h651 | h651
            · linarith only [h651, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h653 | h653
              · linarith only [h653, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h647, h653, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h650, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h657 | h657
          · rcases p0_3 (m.d 4 5) (by simp) with h658 | h658
            · linarith only [h658, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h660 | h660
              · linarith only [h649, h660, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h660, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h657, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h664 | h664
        · rcases p0_3 (m.d 3 5) (by simp) with h665 | h665
          · rcases p0_3 (m.d 4 5) (by simp) with h666 | h666
            · linarith only [h666, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h668 | h668
              · linarith only [h648, h668, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h664, h668, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · linarith only [h665, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h672 | h672
          · rcases p0_3 (m.d 4 5) (by simp) with h673 | h673
            · linarith only [h673, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h675 | h675
              · linarith only [h648, h675, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h675, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h672, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h679 | h679
      · rcases p0_3 (m.d 2 5) (by simp) with h680 | h680
        · rcases p0_3 (m.d 3 5) (by simp) with h681 | h681
          · rcases p0_3 (m.d 4 5) (by simp) with h682 | h682
            · linarith only [h682, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h684 | h684
              · linarith only [h647, h684, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h679, h684, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h681, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h688 | h688
          · rcases p0_3 (m.d 4 5) (by simp) with h689 | h689
            · linarith only [h689, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h691 | h691
              · linarith only [h647, h691, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h691, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h688, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h695 | h695
        · rcases p0_3 (m.d 3 5) (by simp) with h696 | h696
          · rcases p0_3 (m.d 4 5) (by simp) with h697 | h697
            · linarith only [h697, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h699 | h699
              · linarith only [h647, h699, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h695, h699, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · linarith only [h696, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h703 | h703
          · rcases p0_3 (m.d 4 5) (by simp) with h704 | h704
            · linarith only [h704, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h706 | h706
              · linarith only [h647, h706, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h706, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h703, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h711 | h711
    · linarith only [h711, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h713 | h713
      · rcases p0_3 (m.d 2 5) (by simp) with h714 | h714
        · rcases p0_3 (m.d 3 5) (by simp) with h715 | h715
          · rcases p0_3 (m.d 4 5) (by simp) with h716 | h716
            · rcases p0_3 (m.d 5 6) (by simp) with h717 | h717
              · linarith only [h717, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h713, h717, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h716, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h721 | h721
            · rcases p0_3 (m.d 5 6) (by simp) with h722 | h722
              · linarith only [h722, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h722, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h721, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h726 | h726
          · rcases p0_3 (m.d 4 5) (by simp) with h727 | h727
            · rcases p0_3 (m.d 5 6) (by simp) with h728 | h728
              · linarith only [h728, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h726, h728, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h727, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h732 | h732
            · rcases p0_3 (m.d 5 6) (by simp) with h733 | h733
              · linarith only [h733, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h733, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h732, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h737 | h737
        · rcases p0_3 (m.d 3 5) (by simp) with h738 | h738
          · rcases p0_3 (m.d 4 5) (by simp) with h739 | h739
            · rcases p0_3 (m.d 5 6) (by simp) with h740 | h740
              · linarith only [h740, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h737, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h739, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h744 | h744
            · rcases p0_3 (m.d 5 6) (by simp) with h745 | h745
              · linarith only [h745, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h745, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h744, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h749 | h749
          · rcases p0_3 (m.d 4 5) (by simp) with h750 | h750
            · rcases p0_3 (m.d 5 6) (by simp) with h751 | h751
              · linarith only [h751, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h749, h751, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h750, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h755 | h755
            · rcases p0_3 (m.d 5 6) (by simp) with h756 | h756
              · linarith only [h756, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h756, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h755, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h760 | h760
    · rcases p0_3 (m.d 1 5) (by simp) with h761 | h761
      · linarith only [h761, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h763 | h763
        · rcases p0_3 (m.d 3 5) (by simp) with h764 | h764
          · rcases p0_3 (m.d 4 5) (by simp) with h765 | h765
            · rcases p0_3 (m.d 5 6) (by simp) with h766 | h766
              · linarith only [h766, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h760, h766, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h765, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h770 | h770
            · rcases p0_3 (m.d 5 6) (by simp) with h771 | h771
              · linarith only [h771, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h771, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h770, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h775 | h775
          · rcases p0_3 (m.d 4 5) (by simp) with h776 | h776
            · rcases p0_3 (m.d 5 6) (by simp) with h777 | h777
              · linarith only [h777, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h775, h777, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h776, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h781 | h781
            · rcases p0_3 (m.d 5 6) (by simp) with h782 | h782
              · linarith only [h782, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h782, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h781, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h786 | h786
      · linarith only [h786, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h788 | h788
        · rcases p0_3 (m.d 3 5) (by simp) with h789 | h789
          · rcases p0_3 (m.d 4 5) (by simp) with h790 | h790
            · rcases p0_3 (m.d 5 6) (by simp) with h791 | h791
              · linarith only [h760, h791, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h788, h791, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h790, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h795 | h795
            · rcases p0_3 (m.d 5 6) (by simp) with h796 | h796
              · linarith only [h760, h796, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h788, h796, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h795, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h800 | h800
          · rcases p0_3 (m.d 4 5) (by simp) with h801 | h801
            · rcases p0_3 (m.d 5 6) (by simp) with h802 | h802
              · linarith only [h760, h802, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h800, h802, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h801, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h806 | h806
            · rcases p0_3 (m.d 5 6) (by simp) with h807 | h807
              · linarith only [h760, h807, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h807, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h806, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h811 | h811
    · rcases p0_3 (m.d 1 5) (by simp) with h812 | h812
      · rcases p0_3 (m.d 2 5) (by simp) with h813 | h813
        · linarith only [h813, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h815 | h815
          · rcases p0_3 (m.d 4 5) (by simp) with h816 | h816
            · rcases p0_3 (m.d 5 6) (by simp) with h817 | h817
              · linarith only [h817, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h811, h817, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h816, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h821 | h821
            · rcases p0_3 (m.d 5 6) (by simp) with h822 | h822
              · linarith only [h822, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h822, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h821, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h826 | h826
        · linarith only [h826, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h828 | h828
          · rcases p0_3 (m.d 4 5) (by simp) with h829 | h829
            · rcases p0_3 (m.d 5 6) (by simp) with h830 | h830
              · linarith only [h812, h830, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h828, h830, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h829, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h834 | h834
            · rcases p0_3 (m.d 5 6) (by simp) with h835 | h835
              · linarith only [h812, h835, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h835, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h834, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h839 | h839
      · rcases p0_3 (m.d 2 5) (by simp) with h840 | h840
        · linarith only [h840, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h842 | h842
          · rcases p0_3 (m.d 4 5) (by simp) with h843 | h843
            · rcases p0_3 (m.d 5 6) (by simp) with h844 | h844
              · linarith only [h811, h844, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h839, h844, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h843, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h848 | h848
            · rcases p0_3 (m.d 5 6) (by simp) with h849 | h849
              · linarith only [h811, h849, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h839, h849, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h848, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h853 | h853
        · linarith only [h853, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h855 | h855
          · rcases p0_3 (m.d 4 5) (by simp) with h856 | h856
            · rcases p0_3 (m.d 5 6) (by simp) with h857 | h857
              · linarith only [h811, h857, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h855, h857, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h861 | h861
            · rcases p0_3 (m.d 5 6) (by simp) with h862 | h862
              · linarith only [h811, h862, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h862, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h861, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h866 | h866
    · rcases p0_3 (m.d 1 5) (by simp) with h867 | h867
      · rcases p0_3 (m.d 2 5) (by simp) with h868 | h868
        · rcases p0_3 (m.d 3 5) (by simp) with h869 | h869
          · linarith only [h869, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h871 | h871
            · rcases p0_3 (m.d 5 6) (by simp) with h872 | h872
              · linarith only [h872, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h866, h872, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h871, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h876 | h876
          · linarith only [h876, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 5 6) (by simp) with h879 | h879
              · linarith only [h868, h879, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h879, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h878, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h883 | h883
        · rcases p0_3 (m.d 3 5) (by simp) with h884 | h884
          · linarith only [h884, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h886 | h886
            · rcases p0_3 (m.d 5 6) (by simp) with h887 | h887
              · linarith only [h867, h887, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h883, h887, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h886, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h891 | h891
          · linarith only [h891, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h893 | h893
            · rcases p0_3 (m.d 5 6) (by simp) with h894 | h894
              · linarith only [h867, h894, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h894, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h893, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h898 | h898
      · rcases p0_3 (m.d 2 5) (by simp) with h899 | h899
        · rcases p0_3 (m.d 3 5) (by simp) with h900 | h900
          · linarith only [h900, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h902 | h902
            · rcases p0_3 (m.d 5 6) (by simp) with h903 | h903
              · linarith only [h866, h903, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h898, h903, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h902, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h907 | h907
          · linarith only [h907, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h909 | h909
            · rcases p0_3 (m.d 5 6) (by simp) with h910 | h910
              · linarith only [h866, h910, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h910, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h909, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h914 | h914
        · rcases p0_3 (m.d 3 5) (by simp) with h915 | h915
          · linarith only [h915, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h917 | h917
            · rcases p0_3 (m.d 5 6) (by simp) with h918 | h918
              · linarith only [h866, h918, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h914, h918, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h917, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h922 | h922
          · linarith only [h922, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h924 | h924
            · rcases p0_3 (m.d 5 6) (by simp) with h925 | h925
              · linarith only [h866, h925, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h925, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h924, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAB8_H_I_M_IR (m : N8Model)
    (hb5 : CMSig2_8_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h5bigk := hb5.1
  have h6ehi := hb6.2.1
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 5) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 5) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 5 6) (by simp) with h8 | h8
              · linarith only [h8, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h8, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h11 | h11
              · linarith only [h11, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h11, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · rcases p0_3 (m.d 5 6) (by simp) with h15 | h15
              · linarith only [h15, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h15, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h18 | h18
              · linarith only [h18, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h18, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 5 6) (by simp) with h23 | h23
              · linarith only [h23, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h23, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h26 | h26
              · linarith only [h26, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h26, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · rcases p0_3 (m.d 5 6) (by simp) with h30 | h30
              · linarith only [h30, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h30, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h33 | h33
              · linarith only [h33, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h33, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
    · rcases p0_3 (m.d 1 5) (by simp) with h38 | h38
      · rcases p0_3 (m.d 2 5) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h41 | h41
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases p0_3 (m.d 5 6) (by simp) with h43 | h43
              · linarith only [h43, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h43, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h46 | h46
              · linarith only [h46, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h46, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · rcases p0_3 (m.d 5 6) (by simp) with h50 | h50
              · linarith only [h50, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h50, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h53 | h53
              · linarith only [h53, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h53, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h58 | h58
          · rcases p0_3 (m.d 4 5) (by simp) with h59 | h59
            · rcases p0_3 (m.d 5 6) (by simp) with h60 | h60
              · linarith only [h38, h60, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h60, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h63 | h63
              · linarith only [h38, h63, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h63, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · rcases p0_3 (m.d 5 6) (by simp) with h67 | h67
              · linarith only [h38, h67, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h67, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h70 | h70
              · linarith only [h38, h70, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h70, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h37, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
    · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
      · rcases p0_3 (m.d 2 5) (by simp) with h76 | h76
        · rcases p0_3 (m.d 3 5) (by simp) with h77 | h77
          · linarith only [h77, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h79 | h79
            · rcases p0_3 (m.d 5 6) (by simp) with h80 | h80
              · linarith only [h80, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h80, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h83 | h83
              · linarith only [h83, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h83, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · rcases p0_3 (m.d 5 6) (by simp) with h89 | h89
              · linarith only [h76, h89, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h89, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h92 | h92
              · linarith only [h76, h92, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h92, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 5) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · rcases p0_3 (m.d 5 6) (by simp) with h99 | h99
              · linarith only [h75, h99, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h99, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h102 | h102
              · linarith only [h102, h75, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h102, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · rcases p0_3 (m.d 5 6) (by simp) with h108 | h108
              · linarith only [h108, h75, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h108, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h111 | h111
              · linarith only [h111, h75, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h111, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h74, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h115 | h115
    · rcases p0_3 (m.d 1 5) (by simp) with h116 | h116
      · rcases p0_3 (m.d 2 5) (by simp) with h117 | h117
        · rcases p0_3 (m.d 3 5) (by simp) with h118 | h118
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h121 | h121
              · linarith only [h121, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h121, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h126 | h126
              · linarith only [h118, h126, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h126, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h129 | h129
          · rcases p0_3 (m.d 4 5) (by simp) with h130 | h130
            · linarith only [h130, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h132 | h132
              · linarith only [h117, h132, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h132, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h137 | h137
              · linarith only [h117, h137, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h137, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 5) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h144 | h144
              · linarith only [h116, h144, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h144, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h149 | h149
              · linarith only [h116, h149, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h149, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h155 | h155
              · linarith only [h116, h155, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h155, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h158 | h158
            · linarith only [h158, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h160 | h160
              · linarith only [h116, h160, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h160, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h115, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
    · linarith only [h165, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h167 | h167
      · rcases p0_3 (m.d 2 5) (by simp) with h168 | h168
        · rcases p0_3 (m.d 3 5) (by simp) with h169 | h169
          · rcases p0_3 (m.d 4 5) (by simp) with h170 | h170
            · rcases p0_3 (m.d 5 6) (by simp) with h171 | h171
              · linarith only [h171, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h171, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h174 | h174
              · linarith only [h174, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h174, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h177 | h177
            · rcases p0_3 (m.d 5 6) (by simp) with h178 | h178
              · linarith only [h178, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h178, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h181 | h181
              · linarith only [h181, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h181, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h184 | h184
          · rcases p0_3 (m.d 4 5) (by simp) with h185 | h185
            · rcases p0_3 (m.d 5 6) (by simp) with h186 | h186
              · linarith only [h186, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h186, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h189 | h189
              · linarith only [h189, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h189, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h192 | h192
            · rcases p0_3 (m.d 5 6) (by simp) with h193 | h193
              · linarith only [h193, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h193, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h196 | h196
              · linarith only [h196, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h196, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h167, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h201 | h201
    · rcases p0_3 (m.d 1 5) (by simp) with h202 | h202
      · rcases p0_3 (m.d 2 5) (by simp) with h203 | h203
        · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h205 | h205
          · rcases p0_3 (m.d 4 5) (by simp) with h206 | h206
            · rcases p0_3 (m.d 5 6) (by simp) with h207 | h207
              · linarith only [h207, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h201, h207, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h210 | h210
              · linarith only [h210, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h210, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases p0_3 (m.d 5 6) (by simp) with h214 | h214
              · linarith only [h214, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h214, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h217 | h217
              · linarith only [h217, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h217, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h202, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h221 | h221
      · rcases p0_3 (m.d 2 5) (by simp) with h222 | h222
        · linarith only [h222, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h224 | h224
          · rcases p0_3 (m.d 4 5) (by simp) with h225 | h225
            · rcases p0_3 (m.d 5 6) (by simp) with h226 | h226
              · linarith only [h201, h226, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h226, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h229 | h229
              · linarith only [h201, h229, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h229, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · rcases p0_3 (m.d 5 6) (by simp) with h233 | h233
              · linarith only [h201, h233, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h233, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h236 | h236
              · linarith only [h201, h236, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h236, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h221, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h240 | h240
    · rcases p0_3 (m.d 1 5) (by simp) with h241 | h241
      · rcases p0_3 (m.d 2 5) (by simp) with h242 | h242
        · rcases p0_3 (m.d 3 5) (by simp) with h243 | h243
          · linarith only [h243, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h245 | h245
            · rcases p0_3 (m.d 5 6) (by simp) with h246 | h246
              · linarith only [h246, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h240, h246, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h249 | h249
              · linarith only [h249, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h249, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h254 | h254
            · rcases p0_3 (m.d 5 6) (by simp) with h255 | h255
              · linarith only [h242, h255, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h255, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h258 | h258
              · linarith only [h242, h258, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h258, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h241, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h262 | h262
      · rcases p0_3 (m.d 2 5) (by simp) with h263 | h263
        · rcases p0_3 (m.d 3 5) (by simp) with h264 | h264
          · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h266 | h266
            · rcases p0_3 (m.d 5 6) (by simp) with h267 | h267
              · linarith only [h240, h267, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h267, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h270 | h270
              · linarith only [h240, h270, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h270, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h275 | h275
            · rcases p0_3 (m.d 5 6) (by simp) with h276 | h276
              · linarith only [h240, h276, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h276, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h279 | h279
              · linarith only [h240, h279, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h279, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h262, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h283 | h283
    · rcases p0_3 (m.d 1 5) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 5) (by simp) with h285 | h285
        · rcases p0_3 (m.d 3 5) (by simp) with h286 | h286
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h289 | h289
              · linarith only [h289, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h283, h289, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h292 | h292
            · linarith only [h292, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h294 | h294
              · linarith only [h286, h294, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h294, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h297 | h297
          · rcases p0_3 (m.d 4 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h300 | h300
              · linarith only [h285, h300, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h300, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h303 | h303
            · linarith only [h303, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h305 | h305
              · linarith only [h285, h305, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h305, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h284, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h309 | h309
      · rcases p0_3 (m.d 2 5) (by simp) with h310 | h310
        · rcases p0_3 (m.d 3 5) (by simp) with h311 | h311
          · rcases p0_3 (m.d 4 5) (by simp) with h312 | h312
            · linarith only [h312, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h314 | h314
              · linarith only [h283, h314, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h314, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h319 | h319
              · linarith only [h283, h319, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h319, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h322 | h322
          · rcases p0_3 (m.d 4 5) (by simp) with h323 | h323
            · linarith only [h323, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h325 | h325
              · linarith only [h283, h325, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h325, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h328 | h328
            · linarith only [h328, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h330 | h330
              · linarith only [h283, h330, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h330, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h309, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h335 | h335
    · linarith only [h335, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h337 | h337
      · rcases p0_3 (m.d 2 5) (by simp) with h338 | h338
        · rcases p0_3 (m.d 3 5) (by simp) with h339 | h339
          · rcases p0_3 (m.d 4 5) (by simp) with h340 | h340
            · rcases p0_3 (m.d 5 6) (by simp) with h341 | h341
              · linarith only [h341, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h341, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h344 | h344
              · linarith only [h344, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h344, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h347 | h347
            · rcases p0_3 (m.d 5 6) (by simp) with h348 | h348
              · linarith only [h348, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h348, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h351 | h351
              · linarith only [h351, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h351, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h338, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h355 | h355
        · rcases p0_3 (m.d 3 5) (by simp) with h356 | h356
          · rcases p0_3 (m.d 4 5) (by simp) with h357 | h357
            · rcases p0_3 (m.d 5 6) (by simp) with h358 | h358
              · linarith only [h358, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h358, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h361 | h361
              · linarith only [h361, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h361, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h364 | h364
            · rcases p0_3 (m.d 5 6) (by simp) with h365 | h365
              · linarith only [h365, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h365, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h368 | h368
              · linarith only [h368, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h368, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h355, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
    · rcases p0_3 (m.d 1 5) (by simp) with h373 | h373
      · linarith only [h373, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h375 | h375
        · rcases p0_3 (m.d 3 5) (by simp) with h376 | h376
          · rcases p0_3 (m.d 4 5) (by simp) with h377 | h377
            · rcases p0_3 (m.d 5 6) (by simp) with h378 | h378
              · linarith only [h378, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h372, h378, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h381 | h381
              · linarith only [h381, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h381, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h384 | h384
            · rcases p0_3 (m.d 5 6) (by simp) with h385 | h385
              · linarith only [h385, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h385, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h388 | h388
              · linarith only [h388, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h388, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h375, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h392 | h392
      · linarith only [h392, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h394 | h394
        · rcases p0_3 (m.d 3 5) (by simp) with h395 | h395
          · rcases p0_3 (m.d 4 5) (by simp) with h396 | h396
            · rcases p0_3 (m.d 5 6) (by simp) with h397 | h397
              · linarith only [h372, h397, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h397, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h400 | h400
              · linarith only [h372, h400, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h400, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h403 | h403
            · rcases p0_3 (m.d 5 6) (by simp) with h404 | h404
              · linarith only [h372, h404, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h404, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h407 | h407
              · linarith only [h372, h407, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h407, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h394, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h412 | h412
    · rcases p0_3 (m.d 1 5) (by simp) with h413 | h413
      · rcases p0_3 (m.d 2 5) (by simp) with h414 | h414
        · rcases p0_3 (m.d 3 5) (by simp) with h415 | h415
          · linarith only [h415, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h417 | h417
            · rcases p0_3 (m.d 5 6) (by simp) with h418 | h418
              · linarith only [h418, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h412, h418, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h421 | h421
              · linarith only [h421, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h421, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h414, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h425 | h425
        · rcases p0_3 (m.d 3 5) (by simp) with h426 | h426
          · linarith only [h426, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h428 | h428
            · rcases p0_3 (m.d 5 6) (by simp) with h429 | h429
              · linarith only [h413, h429, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h429, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h432 | h432
              · linarith only [h413, h432, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h432, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h425, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h436 | h436
      · rcases p0_3 (m.d 2 5) (by simp) with h437 | h437
        · rcases p0_3 (m.d 3 5) (by simp) with h438 | h438
          · linarith only [h438, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h440 | h440
            · rcases p0_3 (m.d 5 6) (by simp) with h441 | h441
              · linarith only [h412, h441, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h436, h441, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h444 | h444
              · linarith only [h412, h444, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h444, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h437, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h448 | h448
        · rcases p0_3 (m.d 3 5) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h451 | h451
            · rcases p0_3 (m.d 5 6) (by simp) with h452 | h452
              · linarith only [h412, h452, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h452, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h455 | h455
              · linarith only [h412, h455, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h455, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h448, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h459 | h459
    · rcases p0_3 (m.d 1 5) (by simp) with h460 | h460
      · rcases p0_3 (m.d 2 5) (by simp) with h461 | h461
        · rcases p0_3 (m.d 3 5) (by simp) with h462 | h462
          · rcases p0_3 (m.d 4 5) (by simp) with h463 | h463
            · linarith only [h463, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h465 | h465
              · linarith only [h465, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h459, h465, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · linarith only [h468, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h470 | h470
              · linarith only [h462, h470, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h470, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h474 | h474
        · rcases p0_3 (m.d 3 5) (by simp) with h475 | h475
          · rcases p0_3 (m.d 4 5) (by simp) with h476 | h476
            · linarith only [h476, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h478 | h478
              · linarith only [h460, h478, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h481 | h481
            · linarith only [h481, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h483 | h483
              · linarith only [h460, h483, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h483, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h474, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
      · rcases p0_3 (m.d 2 5) (by simp) with h488 | h488
        · rcases p0_3 (m.d 3 5) (by simp) with h489 | h489
          · rcases p0_3 (m.d 4 5) (by simp) with h490 | h490
            · linarith only [h490, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h492 | h492
              · linarith only [h459, h492, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h487, h492, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h495 | h495
            · linarith only [h495, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h497 | h497
              · linarith only [h459, h497, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h497, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h501 | h501
        · rcases p0_3 (m.d 3 5) (by simp) with h502 | h502
          · rcases p0_3 (m.d 4 5) (by simp) with h503 | h503
            · linarith only [h503, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h505 | h505
              · linarith only [h459, h505, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h508 | h508
            · linarith only [h508, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h510 | h510
              · linarith only [h459, h510, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h510, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h501, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h515 | h515
    · linarith only [h515, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h517 | h517
      · rcases p0_3 (m.d 2 5) (by simp) with h518 | h518
        · rcases p0_3 (m.d 3 5) (by simp) with h519 | h519
          · rcases p0_3 (m.d 4 5) (by simp) with h520 | h520
            · rcases p0_3 (m.d 5 6) (by simp) with h521 | h521
              · linarith only [h521, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h517, h521, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h524 | h524
              · linarith only [h524, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h524, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h519, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h528 | h528
          · rcases p0_3 (m.d 4 5) (by simp) with h529 | h529
            · rcases p0_3 (m.d 5 6) (by simp) with h530 | h530
              · linarith only [h530, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h530, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h533 | h533
              · linarith only [h533, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h533, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h528, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h537 | h537
        · rcases p0_3 (m.d 3 5) (by simp) with h538 | h538
          · rcases p0_3 (m.d 4 5) (by simp) with h539 | h539
            · rcases p0_3 (m.d 5 6) (by simp) with h540 | h540
              · linarith only [h540, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h537, h540, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h543 | h543
              · linarith only [h543, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h543, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h538, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h547 | h547
          · rcases p0_3 (m.d 4 5) (by simp) with h548 | h548
            · rcases p0_3 (m.d 5 6) (by simp) with h549 | h549
              · linarith only [h549, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h549, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h552 | h552
              · linarith only [h552, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h552, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h547, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h556 | h556
    · rcases p0_3 (m.d 1 5) (by simp) with h557 | h557
      · linarith only [h557, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h559 | h559
        · rcases p0_3 (m.d 3 5) (by simp) with h560 | h560
          · rcases p0_3 (m.d 4 5) (by simp) with h561 | h561
            · rcases p0_3 (m.d 5 6) (by simp) with h562 | h562
              · linarith only [h562, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h556, h562, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h565 | h565
              · linarith only [h565, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h556, h565, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h560, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h569 | h569
          · rcases p0_3 (m.d 4 5) (by simp) with h570 | h570
            · rcases p0_3 (m.d 5 6) (by simp) with h571 | h571
              · linarith only [h571, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h571, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h574 | h574
              · linarith only [h574, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h574, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h569, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h578 | h578
      · linarith only [h578, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h580 | h580
        · rcases p0_3 (m.d 3 5) (by simp) with h581 | h581
          · rcases p0_3 (m.d 4 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 5 6) (by simp) with h583 | h583
              · linarith only [h556, h583, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h580, h583, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h586 | h586
              · linarith only [h556, h586, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h586, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h581, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h590 | h590
          · rcases p0_3 (m.d 4 5) (by simp) with h591 | h591
            · rcases p0_3 (m.d 5 6) (by simp) with h592 | h592
              · linarith only [h556, h592, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h592, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h595 | h595
              · linarith only [h556, h595, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h595, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h590, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h599 | h599
    · rcases p0_3 (m.d 1 5) (by simp) with h600 | h600
      · rcases p0_3 (m.d 2 5) (by simp) with h601 | h601
        · linarith only [h601, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h603 | h603
          · rcases p0_3 (m.d 4 5) (by simp) with h604 | h604
            · rcases p0_3 (m.d 5 6) (by simp) with h605 | h605
              · linarith only [h605, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h599, h605, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h608 | h608
              · linarith only [h608, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h608, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h603, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h612 | h612
        · linarith only [h612, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h614 | h614
          · rcases p0_3 (m.d 4 5) (by simp) with h615 | h615
            · rcases p0_3 (m.d 5 6) (by simp) with h616 | h616
              · linarith only [h600, h616, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h616, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h619 | h619
              · linarith only [h600, h619, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h619, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h614, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h623 | h623
      · rcases p0_3 (m.d 2 5) (by simp) with h624 | h624
        · linarith only [h624, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h626 | h626
          · rcases p0_3 (m.d 4 5) (by simp) with h627 | h627
            · rcases p0_3 (m.d 5 6) (by simp) with h628 | h628
              · linarith only [h599, h628, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h623, h628, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h631 | h631
              · linarith only [h599, h631, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h631, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h626, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h635 | h635
        · linarith only [h635, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h637 | h637
          · rcases p0_3 (m.d 4 5) (by simp) with h638 | h638
            · rcases p0_3 (m.d 5 6) (by simp) with h639 | h639
              · linarith only [h599, h639, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h639, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h642 | h642
              · linarith only [h599, h642, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h642, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h637, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h647 | h647
    · rcases p0_3 (m.d 1 5) (by simp) with h648 | h648
      · rcases p0_3 (m.d 2 5) (by simp) with h649 | h649
        · rcases p0_3 (m.d 3 5) (by simp) with h650 | h650
          · rcases p0_3 (m.d 4 5) (by simp) with h651 | h651
            · linarith only [h651, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h653 | h653
              · linarith only [h653, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h647, h653, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h650, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h657 | h657
          · rcases p0_3 (m.d 4 5) (by simp) with h658 | h658
            · linarith only [h658, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h660 | h660
              · linarith only [h649, h660, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h660, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h657, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h664 | h664
        · rcases p0_3 (m.d 3 5) (by simp) with h665 | h665
          · rcases p0_3 (m.d 4 5) (by simp) with h666 | h666
            · linarith only [h666, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h668 | h668
              · linarith only [h648, h668, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h664, h668, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · linarith only [h665, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h672 | h672
          · rcases p0_3 (m.d 4 5) (by simp) with h673 | h673
            · linarith only [h673, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h675 | h675
              · linarith only [h648, h675, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h675, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h672, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h679 | h679
      · rcases p0_3 (m.d 2 5) (by simp) with h680 | h680
        · rcases p0_3 (m.d 3 5) (by simp) with h681 | h681
          · rcases p0_3 (m.d 4 5) (by simp) with h682 | h682
            · linarith only [h682, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h684 | h684
              · linarith only [h647, h684, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h679, h684, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h681, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h688 | h688
          · rcases p0_3 (m.d 4 5) (by simp) with h689 | h689
            · linarith only [h689, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h691 | h691
              · linarith only [h647, h691, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h691, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h688, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h695 | h695
        · rcases p0_3 (m.d 3 5) (by simp) with h696 | h696
          · rcases p0_3 (m.d 4 5) (by simp) with h697 | h697
            · linarith only [h697, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h699 | h699
              · linarith only [h647, h699, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h695, h699, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · linarith only [h696, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h703 | h703
          · rcases p0_3 (m.d 4 5) (by simp) with h704 | h704
            · linarith only [h704, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h706 | h706
              · linarith only [h647, h706, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h706, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h703, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h711 | h711
    · linarith only [h711, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h713 | h713
      · rcases p0_3 (m.d 2 5) (by simp) with h714 | h714
        · rcases p0_3 (m.d 3 5) (by simp) with h715 | h715
          · rcases p0_3 (m.d 4 5) (by simp) with h716 | h716
            · rcases p0_3 (m.d 5 6) (by simp) with h717 | h717
              · linarith only [h717, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h713, h717, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h716, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h721 | h721
            · rcases p0_3 (m.d 5 6) (by simp) with h722 | h722
              · linarith only [h722, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h722, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h721, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h726 | h726
          · rcases p0_3 (m.d 4 5) (by simp) with h727 | h727
            · rcases p0_3 (m.d 5 6) (by simp) with h728 | h728
              · linarith only [h728, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h726, h728, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h727, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h732 | h732
            · rcases p0_3 (m.d 5 6) (by simp) with h733 | h733
              · linarith only [h733, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h733, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h732, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h737 | h737
        · rcases p0_3 (m.d 3 5) (by simp) with h738 | h738
          · rcases p0_3 (m.d 4 5) (by simp) with h739 | h739
            · rcases p0_3 (m.d 5 6) (by simp) with h740 | h740
              · linarith only [h740, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h737, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h739, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h744 | h744
            · rcases p0_3 (m.d 5 6) (by simp) with h745 | h745
              · linarith only [h745, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h737, h745, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h744, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h749 | h749
          · rcases p0_3 (m.d 4 5) (by simp) with h750 | h750
            · rcases p0_3 (m.d 5 6) (by simp) with h751 | h751
              · linarith only [h751, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h749, h751, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h750, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h755 | h755
            · rcases p0_3 (m.d 5 6) (by simp) with h756 | h756
              · linarith only [h756, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h756, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h755, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h760 | h760
    · rcases p0_3 (m.d 1 5) (by simp) with h761 | h761
      · linarith only [h761, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h763 | h763
        · rcases p0_3 (m.d 3 5) (by simp) with h764 | h764
          · rcases p0_3 (m.d 4 5) (by simp) with h765 | h765
            · rcases p0_3 (m.d 5 6) (by simp) with h766 | h766
              · linarith only [h766, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h760, h766, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h765, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h770 | h770
            · rcases p0_3 (m.d 5 6) (by simp) with h771 | h771
              · linarith only [h771, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h771, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h770, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h775 | h775
          · rcases p0_3 (m.d 4 5) (by simp) with h776 | h776
            · rcases p0_3 (m.d 5 6) (by simp) with h777 | h777
              · linarith only [h777, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h775, h777, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h776, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h781 | h781
            · rcases p0_3 (m.d 5 6) (by simp) with h782 | h782
              · linarith only [h782, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h782, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h781, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h786 | h786
      · linarith only [h786, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h788 | h788
        · rcases p0_3 (m.d 3 5) (by simp) with h789 | h789
          · rcases p0_3 (m.d 4 5) (by simp) with h790 | h790
            · rcases p0_3 (m.d 5 6) (by simp) with h791 | h791
              · linarith only [h760, h791, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h788, h791, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h790, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h795 | h795
            · rcases p0_3 (m.d 5 6) (by simp) with h796 | h796
              · linarith only [h760, h796, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h788, h796, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h795, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h800 | h800
          · rcases p0_3 (m.d 4 5) (by simp) with h801 | h801
            · rcases p0_3 (m.d 5 6) (by simp) with h802 | h802
              · linarith only [h760, h802, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h800, h802, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h801, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h806 | h806
            · rcases p0_3 (m.d 5 6) (by simp) with h807 | h807
              · linarith only [h760, h807, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h807, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h806, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h811 | h811
    · rcases p0_3 (m.d 1 5) (by simp) with h812 | h812
      · rcases p0_3 (m.d 2 5) (by simp) with h813 | h813
        · linarith only [h813, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h815 | h815
          · rcases p0_3 (m.d 4 5) (by simp) with h816 | h816
            · rcases p0_3 (m.d 5 6) (by simp) with h817 | h817
              · linarith only [h817, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h811, h817, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h816, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h821 | h821
            · rcases p0_3 (m.d 5 6) (by simp) with h822 | h822
              · linarith only [h822, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h822, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h821, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h826 | h826
        · linarith only [h826, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h828 | h828
          · rcases p0_3 (m.d 4 5) (by simp) with h829 | h829
            · rcases p0_3 (m.d 5 6) (by simp) with h830 | h830
              · linarith only [h812, h830, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h828, h830, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h829, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h834 | h834
            · rcases p0_3 (m.d 5 6) (by simp) with h835 | h835
              · linarith only [h835, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h835, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h834, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h839 | h839
      · rcases p0_3 (m.d 2 5) (by simp) with h840 | h840
        · linarith only [h840, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h842 | h842
          · rcases p0_3 (m.d 4 5) (by simp) with h843 | h843
            · rcases p0_3 (m.d 5 6) (by simp) with h844 | h844
              · linarith only [h811, h844, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h839, h844, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h843, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h848 | h848
            · rcases p0_3 (m.d 5 6) (by simp) with h849 | h849
              · linarith only [h811, h849, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h839, h849, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h848, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h853 | h853
        · linarith only [h853, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h855 | h855
          · rcases p0_3 (m.d 4 5) (by simp) with h856 | h856
            · rcases p0_3 (m.d 5 6) (by simp) with h857 | h857
              · linarith only [h811, h857, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h855, h857, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h861 | h861
            · rcases p0_3 (m.d 5 6) (by simp) with h862 | h862
              · linarith only [h811, h862, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h862, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h861, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h866 | h866
    · rcases p0_3 (m.d 1 5) (by simp) with h867 | h867
      · rcases p0_3 (m.d 2 5) (by simp) with h868 | h868
        · rcases p0_3 (m.d 3 5) (by simp) with h869 | h869
          · linarith only [h869, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h871 | h871
            · rcases p0_3 (m.d 5 6) (by simp) with h872 | h872
              · linarith only [h872, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h866, h872, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h871, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h876 | h876
          · linarith only [h876, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 5 6) (by simp) with h879 | h879
              · linarith only [h868, h879, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h879, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h878, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h883 | h883
        · rcases p0_3 (m.d 3 5) (by simp) with h884 | h884
          · linarith only [h884, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h886 | h886
            · rcases p0_3 (m.d 5 6) (by simp) with h887 | h887
              · linarith only [h867, h887, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h883, h887, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h886, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h891 | h891
          · linarith only [h891, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h893 | h893
            · rcases p0_3 (m.d 5 6) (by simp) with h894 | h894
              · linarith only [h867, h894, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h894, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h893, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h898 | h898
      · rcases p0_3 (m.d 2 5) (by simp) with h899 | h899
        · rcases p0_3 (m.d 3 5) (by simp) with h900 | h900
          · linarith only [h900, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h902 | h902
            · rcases p0_3 (m.d 5 6) (by simp) with h903 | h903
              · linarith only [h866, h903, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h898, h903, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h902, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h907 | h907
          · linarith only [h907, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h909 | h909
            · rcases p0_3 (m.d 5 6) (by simp) with h910 | h910
              · linarith only [h866, h910, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h898, h910, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h909, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h914 | h914
        · rcases p0_3 (m.d 3 5) (by simp) with h915 | h915
          · linarith only [h915, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h917 | h917
            · rcases p0_3 (m.d 5 6) (by simp) with h918 | h918
              · linarith only [h866, h918, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h914, h918, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h917, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h922 | h922
          · linarith only [h922, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h924 | h924
            · rcases p0_3 (m.d 5 6) (by simp) with h925 | h925
              · linarith only [h866, h925, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h925, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h924, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAB8_H_I_M_LR (m : N8Model)
    (hb5 : CMSig2_8_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5bigk := hb5.1
  have h6elo := hb6.1
  have h6ehi := hb6.2.2.1
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  have u6ehi11 := h6ehi (m.d 5 6) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 5) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 5) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 5 6) (by simp) with h8 | h8
              · linarith only [h8, hc15, hlam, hphi, ht56, p0_1, u6elo5]
              · linarith only [h8, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h11 | h11
              · linarith only [h11, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h11, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · rcases p0_3 (m.d 5 6) (by simp) with h15 | h15
              · linarith only [h15, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h15, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h18 | h18
              · linarith only [h18, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h18, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 5 6) (by simp) with h23 | h23
              · linarith only [h23, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h23, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h26 | h26
              · linarith only [h26, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h26, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · rcases p0_3 (m.d 5 6) (by simp) with h30 | h30
              · linarith only [h30, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h30, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h33 | h33
              · linarith only [h33, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h33, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
    · rcases p0_3 (m.d 1 5) (by simp) with h38 | h38
      · rcases p0_3 (m.d 2 5) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h41 | h41
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases p0_3 (m.d 5 6) (by simp) with h43 | h43
              · linarith only [h43, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h43, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h46 | h46
              · linarith only [h46, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h46, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · rcases p0_3 (m.d 5 6) (by simp) with h50 | h50
              · linarith only [h50, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h50, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h53 | h53
              · linarith only [h53, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h53, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
      · rcases p0_3 (m.d 2 5) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h58 | h58
          · rcases p0_3 (m.d 4 5) (by simp) with h59 | h59
            · rcases p0_3 (m.d 5 6) (by simp) with h60 | h60
              · linarith only [h38, h60, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h60, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h63 | h63
              · linarith only [h63, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h63, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · rcases p0_3 (m.d 5 6) (by simp) with h67 | h67
              · linarith only [h67, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h67, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h70 | h70
              · linarith only [h70, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h70, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
    · linarith only [h37, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
    · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
      · rcases p0_3 (m.d 2 5) (by simp) with h76 | h76
        · rcases p0_3 (m.d 3 5) (by simp) with h77 | h77
          · linarith only [h77, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h79 | h79
            · rcases p0_3 (m.d 5 6) (by simp) with h80 | h80
              · linarith only [h80, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h80, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h83 | h83
              · linarith only [h83, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h83, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · rcases p0_3 (m.d 5 6) (by simp) with h89 | h89
              · linarith only [h76, h89, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h89, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h92 | h92
              · linarith only [h92, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h92, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
      · rcases p0_3 (m.d 2 5) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 5) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · rcases p0_3 (m.d 5 6) (by simp) with h99 | h99
              · linarith only [h75, h99, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h99, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h102 | h102
              · linarith only [h102, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h102, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · rcases p0_3 (m.d 5 6) (by simp) with h108 | h108
              · linarith only [h108, h95, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h108, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h111 | h111
              · linarith only [h111, h95, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h111, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
    · linarith only [h74, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h115 | h115
    · rcases p0_3 (m.d 1 5) (by simp) with h116 | h116
      · rcases p0_3 (m.d 2 5) (by simp) with h117 | h117
        · rcases p0_3 (m.d 3 5) (by simp) with h118 | h118
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h121 | h121
              · linarith only [h121, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h121, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h126 | h126
              · linarith only [h118, h126, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h126, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h129 | h129
          · rcases p0_3 (m.d 4 5) (by simp) with h130 | h130
            · linarith only [h130, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h132 | h132
              · linarith only [h117, h132, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h132, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h137 | h137
              · linarith only [h129, h137, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h137, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
      · rcases p0_3 (m.d 2 5) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 5) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h144 | h144
              · linarith only [h116, h144, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h144, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h149 | h149
              · linarith only [h141, h149, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h149, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h155 | h155
              · linarith only [h140, h155, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h155, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h158 | h158
            · linarith only [h158, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h160 | h160
              · linarith only [h152, h160, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h160, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
    · linarith only [h115, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
    · linarith only [h165, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h167 | h167
      · rcases p0_3 (m.d 2 5) (by simp) with h168 | h168
        · rcases p0_3 (m.d 3 5) (by simp) with h169 | h169
          · rcases p0_3 (m.d 4 5) (by simp) with h170 | h170
            · rcases p0_3 (m.d 5 6) (by simp) with h171 | h171
              · linarith only [h171, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h171, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h174 | h174
              · linarith only [h174, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h174, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h177 | h177
            · rcases p0_3 (m.d 5 6) (by simp) with h178 | h178
              · linarith only [h178, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h178, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h181 | h181
              · linarith only [h181, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h181, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h184 | h184
          · rcases p0_3 (m.d 4 5) (by simp) with h185 | h185
            · rcases p0_3 (m.d 5 6) (by simp) with h186 | h186
              · linarith only [h186, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h186, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h189 | h189
              · linarith only [h189, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h189, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h192 | h192
            · rcases p0_3 (m.d 5 6) (by simp) with h193 | h193
              · linarith only [h193, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h193, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h196 | h196
              · linarith only [h196, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h196, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
      · linarith only [h167, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h201 | h201
    · rcases p0_3 (m.d 1 5) (by simp) with h202 | h202
      · rcases p0_3 (m.d 2 5) (by simp) with h203 | h203
        · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h205 | h205
          · rcases p0_3 (m.d 4 5) (by simp) with h206 | h206
            · rcases p0_3 (m.d 5 6) (by simp) with h207 | h207
              · linarith only [h207, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h201, h207, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h210 | h210
              · linarith only [h210, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h210, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases p0_3 (m.d 5 6) (by simp) with h214 | h214
              · linarith only [h214, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h214, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h217 | h217
              · linarith only [h217, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h217, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
      · linarith only [h202, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h221 | h221
      · rcases p0_3 (m.d 2 5) (by simp) with h222 | h222
        · linarith only [h222, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h224 | h224
          · rcases p0_3 (m.d 4 5) (by simp) with h225 | h225
            · rcases p0_3 (m.d 5 6) (by simp) with h226 | h226
              · linarith only [h201, h226, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h226, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h229 | h229
              · linarith only [h229, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h229, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · rcases p0_3 (m.d 5 6) (by simp) with h233 | h233
              · linarith only [h233, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h233, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h236 | h236
              · linarith only [h236, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h236, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
      · linarith only [h221, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h240 | h240
    · rcases p0_3 (m.d 1 5) (by simp) with h241 | h241
      · rcases p0_3 (m.d 2 5) (by simp) with h242 | h242
        · rcases p0_3 (m.d 3 5) (by simp) with h243 | h243
          · linarith only [h243, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h245 | h245
            · rcases p0_3 (m.d 5 6) (by simp) with h246 | h246
              · linarith only [h246, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h240, h246, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h249 | h249
              · linarith only [h249, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h240, h249, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h254 | h254
            · rcases p0_3 (m.d 5 6) (by simp) with h255 | h255
              · linarith only [h242, h255, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h255, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h258 | h258
              · linarith only [h258, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h258, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
      · linarith only [h241, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h262 | h262
      · rcases p0_3 (m.d 2 5) (by simp) with h263 | h263
        · rcases p0_3 (m.d 3 5) (by simp) with h264 | h264
          · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h266 | h266
            · rcases p0_3 (m.d 5 6) (by simp) with h267 | h267
              · linarith only [h240, h267, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h267, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h270 | h270
              · linarith only [h270, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h270, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h275 | h275
            · rcases p0_3 (m.d 5 6) (by simp) with h276 | h276
              · linarith only [h263, h276, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h276, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h279 | h279
              · linarith only [h263, h279, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h279, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
      · linarith only [h262, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h283 | h283
    · rcases p0_3 (m.d 1 5) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 5) (by simp) with h285 | h285
        · rcases p0_3 (m.d 3 5) (by simp) with h286 | h286
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h289 | h289
              · linarith only [h289, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h283, h289, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h292 | h292
            · linarith only [h292, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h294 | h294
              · linarith only [h286, h294, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h294, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h297 | h297
          · rcases p0_3 (m.d 4 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h300 | h300
              · linarith only [h285, h300, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h300, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h303 | h303
            · linarith only [h303, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h305 | h305
              · linarith only [h285, h305, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h305, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
      · linarith only [h284, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h309 | h309
      · rcases p0_3 (m.d 2 5) (by simp) with h310 | h310
        · rcases p0_3 (m.d 3 5) (by simp) with h311 | h311
          · rcases p0_3 (m.d 4 5) (by simp) with h312 | h312
            · linarith only [h312, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h314 | h314
              · linarith only [h283, h314, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h314, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h319 | h319
              · linarith only [h311, h319, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h319, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
        · rcases p0_3 (m.d 3 5) (by simp) with h322 | h322
          · rcases p0_3 (m.d 4 5) (by simp) with h323 | h323
            · linarith only [h323, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h325 | h325
              · linarith only [h310, h325, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h325, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h328 | h328
            · linarith only [h328, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h330 | h330
              · linarith only [h322, h330, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h330, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
      · linarith only [h309, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h335 | h335
    · linarith only [h335, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h337 | h337
      · rcases p0_3 (m.d 2 5) (by simp) with h338 | h338
        · rcases p0_3 (m.d 3 5) (by simp) with h339 | h339
          · rcases p0_3 (m.d 4 5) (by simp) with h340 | h340
            · rcases p0_3 (m.d 5 6) (by simp) with h341 | h341
              · linarith only [h341, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h341, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h344 | h344
              · linarith only [h344, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h344, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h347 | h347
            · rcases p0_3 (m.d 5 6) (by simp) with h348 | h348
              · linarith only [h348, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h348, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h351 | h351
              · linarith only [h351, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h351, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h338, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h355 | h355
        · rcases p0_3 (m.d 3 5) (by simp) with h356 | h356
          · rcases p0_3 (m.d 4 5) (by simp) with h357 | h357
            · rcases p0_3 (m.d 5 6) (by simp) with h358 | h358
              · linarith only [h358, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h358, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h361 | h361
              · linarith only [h361, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h361, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h364 | h364
            · rcases p0_3 (m.d 5 6) (by simp) with h365 | h365
              · linarith only [h365, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h365, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h368 | h368
              · linarith only [h368, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h368, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h355, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
    · rcases p0_3 (m.d 1 5) (by simp) with h373 | h373
      · linarith only [h373, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h375 | h375
        · rcases p0_3 (m.d 3 5) (by simp) with h376 | h376
          · rcases p0_3 (m.d 4 5) (by simp) with h377 | h377
            · rcases p0_3 (m.d 5 6) (by simp) with h378 | h378
              · linarith only [h378, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h372, h378, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h381 | h381
              · linarith only [h381, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h381, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h384 | h384
            · rcases p0_3 (m.d 5 6) (by simp) with h385 | h385
              · linarith only [h385, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h385, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h388 | h388
              · linarith only [h388, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h388, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h375, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h392 | h392
      · linarith only [h392, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h394 | h394
        · rcases p0_3 (m.d 3 5) (by simp) with h395 | h395
          · rcases p0_3 (m.d 4 5) (by simp) with h396 | h396
            · rcases p0_3 (m.d 5 6) (by simp) with h397 | h397
              · linarith only [h372, h397, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h397, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h400 | h400
              · linarith only [h372, h400, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h400, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h403 | h403
            · rcases p0_3 (m.d 5 6) (by simp) with h404 | h404
              · linarith only [h372, h404, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h404, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h407 | h407
              · linarith only [h372, h407, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h407, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h394, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h412 | h412
    · rcases p0_3 (m.d 1 5) (by simp) with h413 | h413
      · rcases p0_3 (m.d 2 5) (by simp) with h414 | h414
        · rcases p0_3 (m.d 3 5) (by simp) with h415 | h415
          · linarith only [h415, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h417 | h417
            · rcases p0_3 (m.d 5 6) (by simp) with h418 | h418
              · linarith only [h418, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h412, h418, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h421 | h421
              · linarith only [h421, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h421, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h414, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h425 | h425
        · rcases p0_3 (m.d 3 5) (by simp) with h426 | h426
          · linarith only [h426, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h428 | h428
            · rcases p0_3 (m.d 5 6) (by simp) with h429 | h429
              · linarith only [h413, h429, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h429, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h432 | h432
              · linarith only [h432, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h432, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h425, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h436 | h436
      · rcases p0_3 (m.d 2 5) (by simp) with h437 | h437
        · rcases p0_3 (m.d 3 5) (by simp) with h438 | h438
          · linarith only [h438, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h440 | h440
            · rcases p0_3 (m.d 5 6) (by simp) with h441 | h441
              · linarith only [h412, h441, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h436, h441, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h444 | h444
              · linarith only [h412, h444, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h444, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h437, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h448 | h448
        · rcases p0_3 (m.d 3 5) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h451 | h451
            · rcases p0_3 (m.d 5 6) (by simp) with h452 | h452
              · linarith only [h412, h452, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h452, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h455 | h455
              · linarith only [h412, h455, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h455, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h448, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h459 | h459
    · rcases p0_3 (m.d 1 5) (by simp) with h460 | h460
      · rcases p0_3 (m.d 2 5) (by simp) with h461 | h461
        · rcases p0_3 (m.d 3 5) (by simp) with h462 | h462
          · rcases p0_3 (m.d 4 5) (by simp) with h463 | h463
            · linarith only [h463, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h465 | h465
              · linarith only [h465, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h459, h465, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · linarith only [h468, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h470 | h470
              · linarith only [h462, h470, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h470, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h474 | h474
        · rcases p0_3 (m.d 3 5) (by simp) with h475 | h475
          · rcases p0_3 (m.d 4 5) (by simp) with h476 | h476
            · linarith only [h476, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h478 | h478
              · linarith only [h460, h478, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h481 | h481
            · linarith only [h481, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h483 | h483
              · linarith only [h475, h483, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h483, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h474, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
      · rcases p0_3 (m.d 2 5) (by simp) with h488 | h488
        · rcases p0_3 (m.d 3 5) (by simp) with h489 | h489
          · rcases p0_3 (m.d 4 5) (by simp) with h490 | h490
            · linarith only [h490, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h492 | h492
              · linarith only [h459, h492, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h487, h492, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h495 | h495
            · linarith only [h495, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h497 | h497
              · linarith only [h489, h497, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h497, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h501 | h501
        · rcases p0_3 (m.d 3 5) (by simp) with h502 | h502
          · rcases p0_3 (m.d 4 5) (by simp) with h503 | h503
            · linarith only [h503, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h505 | h505
              · linarith only [h487, h505, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · rcases p0_3 (m.d 4 5) (by simp) with h508 | h508
            · linarith only [h508, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h510 | h510
              · linarith only [h502, h510, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h510, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
        · linarith only [h501, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h515 | h515
    · linarith only [h515, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h517 | h517
      · rcases p0_3 (m.d 2 5) (by simp) with h518 | h518
        · rcases p0_3 (m.d 3 5) (by simp) with h519 | h519
          · rcases p0_3 (m.d 4 5) (by simp) with h520 | h520
            · rcases p0_3 (m.d 5 6) (by simp) with h521 | h521
              · linarith only [h521, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h517, h521, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h524 | h524
              · linarith only [h524, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h524, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h519, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h528 | h528
          · rcases p0_3 (m.d 4 5) (by simp) with h529 | h529
            · rcases p0_3 (m.d 5 6) (by simp) with h530 | h530
              · linarith only [h530, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h530, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h533 | h533
              · linarith only [h533, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h533, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h528, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h537 | h537
        · rcases p0_3 (m.d 3 5) (by simp) with h538 | h538
          · rcases p0_3 (m.d 4 5) (by simp) with h539 | h539
            · rcases p0_3 (m.d 5 6) (by simp) with h540 | h540
              · linarith only [h540, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h537, h540, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h543 | h543
              · linarith only [h543, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h543, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h538, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h547 | h547
          · rcases p0_3 (m.d 4 5) (by simp) with h548 | h548
            · rcases p0_3 (m.d 5 6) (by simp) with h549 | h549
              · linarith only [h549, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h549, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h552 | h552
              · linarith only [h552, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h552, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h547, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h556 | h556
    · rcases p0_3 (m.d 1 5) (by simp) with h557 | h557
      · linarith only [h557, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h559 | h559
        · rcases p0_3 (m.d 3 5) (by simp) with h560 | h560
          · rcases p0_3 (m.d 4 5) (by simp) with h561 | h561
            · rcases p0_3 (m.d 5 6) (by simp) with h562 | h562
              · linarith only [h562, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h556, h562, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h565 | h565
              · linarith only [h565, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h565, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h560, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h569 | h569
          · rcases p0_3 (m.d 4 5) (by simp) with h570 | h570
            · rcases p0_3 (m.d 5 6) (by simp) with h571 | h571
              · linarith only [h571, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h571, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h574 | h574
              · linarith only [h574, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h574, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h569, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h578 | h578
      · linarith only [h578, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h580 | h580
        · rcases p0_3 (m.d 3 5) (by simp) with h581 | h581
          · rcases p0_3 (m.d 4 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 5 6) (by simp) with h583 | h583
              · linarith only [h556, h583, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h580, h583, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h586 | h586
              · linarith only [h556, h586, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h586, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h581, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h590 | h590
          · rcases p0_3 (m.d 4 5) (by simp) with h591 | h591
            · rcases p0_3 (m.d 5 6) (by simp) with h592 | h592
              · linarith only [h556, h592, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h592, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h595 | h595
              · linarith only [h556, h595, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h595, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h590, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h599 | h599
    · rcases p0_3 (m.d 1 5) (by simp) with h600 | h600
      · rcases p0_3 (m.d 2 5) (by simp) with h601 | h601
        · linarith only [h601, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h603 | h603
          · rcases p0_3 (m.d 4 5) (by simp) with h604 | h604
            · rcases p0_3 (m.d 5 6) (by simp) with h605 | h605
              · linarith only [h605, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h599, h605, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h608 | h608
              · linarith only [h608, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h608, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h603, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h612 | h612
        · linarith only [h612, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h614 | h614
          · rcases p0_3 (m.d 4 5) (by simp) with h615 | h615
            · rcases p0_3 (m.d 5 6) (by simp) with h616 | h616
              · linarith only [h600, h616, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h616, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h619 | h619
              · linarith only [h619, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h619, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h614, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h623 | h623
      · rcases p0_3 (m.d 2 5) (by simp) with h624 | h624
        · linarith only [h624, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h626 | h626
          · rcases p0_3 (m.d 4 5) (by simp) with h627 | h627
            · rcases p0_3 (m.d 5 6) (by simp) with h628 | h628
              · linarith only [h599, h628, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h623, h628, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h631 | h631
              · linarith only [h599, h631, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h631, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h626, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h635 | h635
        · linarith only [h635, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h637 | h637
          · rcases p0_3 (m.d 4 5) (by simp) with h638 | h638
            · rcases p0_3 (m.d 5 6) (by simp) with h639 | h639
              · linarith only [h599, h639, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h639, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · rcases p0_3 (m.d 5 6) (by simp) with h642 | h642
              · linarith only [h599, h642, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h642, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h637, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h647 | h647
    · rcases p0_3 (m.d 1 5) (by simp) with h648 | h648
      · rcases p0_3 (m.d 2 5) (by simp) with h649 | h649
        · rcases p0_3 (m.d 3 5) (by simp) with h650 | h650
          · rcases p0_3 (m.d 4 5) (by simp) with h651 | h651
            · linarith only [h651, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h653 | h653
              · linarith only [h653, hc45, hc56, hlam, hphi, p0_1]
              · linarith only [h647, h653, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · linarith only [h650, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h657 | h657
          · rcases p0_3 (m.d 4 5) (by simp) with h658 | h658
            · linarith only [h658, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h660 | h660
              · linarith only [h649, h660, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h647, h660, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
          · linarith only [h657, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h664 | h664
        · rcases p0_3 (m.d 3 5) (by simp) with h665 | h665
          · rcases p0_3 (m.d 4 5) (by simp) with h666 | h666
            · linarith only [h666, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h668 | h668
              · linarith only [h648, h668, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h664, h668, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · linarith only [h665, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h672 | h672
          · rcases p0_3 (m.d 4 5) (by simp) with h673 | h673
            · linarith only [h673, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h675 | h675
              · linarith only [h648, h675, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h675, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h672, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h679 | h679
      · rcases p0_3 (m.d 2 5) (by simp) with h680 | h680
        · rcases p0_3 (m.d 3 5) (by simp) with h681 | h681
          · rcases p0_3 (m.d 4 5) (by simp) with h682 | h682
            · linarith only [h682, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h684 | h684
              · linarith only [h647, h684, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h679, h684, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
          · linarith only [h681, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h688 | h688
          · rcases p0_3 (m.d 4 5) (by simp) with h689 | h689
            · linarith only [h689, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h691 | h691
              · linarith only [h647, h691, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h691, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h688, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h695 | h695
        · rcases p0_3 (m.d 3 5) (by simp) with h696 | h696
          · rcases p0_3 (m.d 4 5) (by simp) with h697 | h697
            · linarith only [h697, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h699 | h699
              · linarith only [h647, h699, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h695, h699, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
          · linarith only [h696, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h703 | h703
          · rcases p0_3 (m.d 4 5) (by simp) with h704 | h704
            · linarith only [h704, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h706 | h706
              · linarith only [h679, h706, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h706, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
          · linarith only [h703, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h711 | h711
    · linarith only [h711, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h713 | h713
      · rcases p0_3 (m.d 2 5) (by simp) with h714 | h714
        · rcases p0_3 (m.d 3 5) (by simp) with h715 | h715
          · rcases p0_3 (m.d 4 5) (by simp) with h716 | h716
            · rcases p0_3 (m.d 5 6) (by simp) with h717 | h717
              · linarith only [h717, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h713, h717, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · linarith only [h716, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h721 | h721
            · rcases p0_3 (m.d 5 6) (by simp) with h722 | h722
              · linarith only [h722, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h722, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h721, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h726 | h726
          · rcases p0_3 (m.d 4 5) (by simp) with h727 | h727
            · rcases p0_3 (m.d 5 6) (by simp) with h728 | h728
              · linarith only [h728, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h726, h728, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · linarith only [h727, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h732 | h732
            · rcases p0_3 (m.d 5 6) (by simp) with h733 | h733
              · linarith only [h733, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h733, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h732, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h737 | h737
        · rcases p0_3 (m.d 3 5) (by simp) with h738 | h738
          · rcases p0_3 (m.d 4 5) (by simp) with h739 | h739
            · rcases p0_3 (m.d 5 6) (by simp) with h740 | h740
              · linarith only [h740, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h737, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · linarith only [h739, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h744 | h744
            · rcases p0_3 (m.d 5 6) (by simp) with h745 | h745
              · linarith only [h745, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h737, h745, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · linarith only [h744, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h749 | h749
          · rcases p0_3 (m.d 4 5) (by simp) with h750 | h750
            · rcases p0_3 (m.d 5 6) (by simp) with h751 | h751
              · linarith only [h751, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h749, h751, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · linarith only [h750, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h755 | h755
            · rcases p0_3 (m.d 5 6) (by simp) with h756 | h756
              · linarith only [h756, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h756, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h755, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h760 | h760
    · rcases p0_3 (m.d 1 5) (by simp) with h761 | h761
      · linarith only [h761, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h763 | h763
        · rcases p0_3 (m.d 3 5) (by simp) with h764 | h764
          · rcases p0_3 (m.d 4 5) (by simp) with h765 | h765
            · rcases p0_3 (m.d 5 6) (by simp) with h766 | h766
              · linarith only [h766, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h760, h766, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · linarith only [h765, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h770 | h770
            · rcases p0_3 (m.d 5 6) (by simp) with h771 | h771
              · linarith only [h771, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h771, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h770, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h775 | h775
          · rcases p0_3 (m.d 4 5) (by simp) with h776 | h776
            · rcases p0_3 (m.d 5 6) (by simp) with h777 | h777
              · linarith only [h777, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h775, h777, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · linarith only [h776, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h781 | h781
            · rcases p0_3 (m.d 5 6) (by simp) with h782 | h782
              · linarith only [h782, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h782, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h781, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h786 | h786
      · linarith only [h786, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h788 | h788
        · rcases p0_3 (m.d 3 5) (by simp) with h789 | h789
          · rcases p0_3 (m.d 4 5) (by simp) with h790 | h790
            · rcases p0_3 (m.d 5 6) (by simp) with h791 | h791
              · linarith only [h760, h791, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h788, h791, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · linarith only [h790, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h795 | h795
            · rcases p0_3 (m.d 5 6) (by simp) with h796 | h796
              · linarith only [h760, h796, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h796, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h795, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h800 | h800
          · rcases p0_3 (m.d 4 5) (by simp) with h801 | h801
            · rcases p0_3 (m.d 5 6) (by simp) with h802 | h802
              · linarith only [h760, h802, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h800, h802, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · linarith only [h801, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h806 | h806
            · rcases p0_3 (m.d 5 6) (by simp) with h807 | h807
              · linarith only [h760, h807, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h807, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h806, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h811 | h811
    · rcases p0_3 (m.d 1 5) (by simp) with h812 | h812
      · rcases p0_3 (m.d 2 5) (by simp) with h813 | h813
        · linarith only [h813, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h815 | h815
          · rcases p0_3 (m.d 4 5) (by simp) with h816 | h816
            · rcases p0_3 (m.d 5 6) (by simp) with h817 | h817
              · linarith only [h817, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h811, h817, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · linarith only [h816, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h821 | h821
            · rcases p0_3 (m.d 5 6) (by simp) with h822 | h822
              · linarith only [h822, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h822, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h821, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h826 | h826
        · linarith only [h826, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h828 | h828
          · rcases p0_3 (m.d 4 5) (by simp) with h829 | h829
            · rcases p0_3 (m.d 5 6) (by simp) with h830 | h830
              · linarith only [h812, h830, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h828, h830, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · linarith only [h829, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h834 | h834
            · rcases p0_3 (m.d 5 6) (by simp) with h835 | h835
              · linarith only [h812, h835, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h835, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h834, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h839 | h839
      · rcases p0_3 (m.d 2 5) (by simp) with h840 | h840
        · linarith only [h840, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h842 | h842
          · rcases p0_3 (m.d 4 5) (by simp) with h843 | h843
            · rcases p0_3 (m.d 5 6) (by simp) with h844 | h844
              · linarith only [h811, h844, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h839, h844, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · linarith only [h843, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h848 | h848
            · rcases p0_3 (m.d 5 6) (by simp) with h849 | h849
              · linarith only [h849, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h839, h849, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · linarith only [h848, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h853 | h853
        · linarith only [h853, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h855 | h855
          · rcases p0_3 (m.d 4 5) (by simp) with h856 | h856
            · rcases p0_3 (m.d 5 6) (by simp) with h857 | h857
              · linarith only [h839, h857, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h855, h857, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi11]
            · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h861 | h861
            · rcases p0_3 (m.d 5 6) (by simp) with h862 | h862
              · linarith only [h839, h862, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h862, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h861, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h866 | h866
    · rcases p0_3 (m.d 1 5) (by simp) with h867 | h867
      · rcases p0_3 (m.d 2 5) (by simp) with h868 | h868
        · rcases p0_3 (m.d 3 5) (by simp) with h869 | h869
          · linarith only [h869, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h871 | h871
            · rcases p0_3 (m.d 5 6) (by simp) with h872 | h872
              · linarith only [h872, hc35, hc56, hlam, hphi, p0_1]
              · linarith only [h866, h872, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi11]
            · linarith only [h871, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h876 | h876
          · linarith only [h876, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 5 6) (by simp) with h879 | h879
              · linarith only [h868, h879, hc25, hc56, hlam, hphi, p0_1]
              · linarith only [h879, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h878, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h883 | h883
        · rcases p0_3 (m.d 3 5) (by simp) with h884 | h884
          · linarith only [h884, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h886 | h886
            · rcases p0_3 (m.d 5 6) (by simp) with h887 | h887
              · linarith only [h867, h887, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h883, h887, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · linarith only [h886, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h891 | h891
          · linarith only [h891, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h893 | h893
            · rcases p0_3 (m.d 5 6) (by simp) with h894 | h894
              · linarith only [h867, h894, hc15, hc56, hlam, hphi, p0_1]
              · linarith only [h894, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h893, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h898 | h898
      · rcases p0_3 (m.d 2 5) (by simp) with h899 | h899
        · rcases p0_3 (m.d 3 5) (by simp) with h900 | h900
          · linarith only [h900, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h902 | h902
            · rcases p0_3 (m.d 5 6) (by simp) with h903 | h903
              · linarith only [h866, h903, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h898, h903, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi11]
            · linarith only [h902, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h907 | h907
          · linarith only [h907, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h909 | h909
            · rcases p0_3 (m.d 5 6) (by simp) with h910 | h910
              · linarith only [h866, h910, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h910, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h909, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h914 | h914
        · rcases p0_3 (m.d 3 5) (by simp) with h915 | h915
          · linarith only [h915, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h917 | h917
            · rcases p0_3 (m.d 5 6) (by simp) with h918 | h918
              · linarith only [h866, h918, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h914, h918, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi11]
            · linarith only [h917, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h922 | h922
          · linarith only [h922, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h924 | h924
            · rcases p0_3 (m.d 5 6) (by simp) with h925 | h925
              · linarith only [h866, h925, hc05, hc56, hlam, hphi, p0_1]
              · linarith only [h925, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
            · linarith only [h924, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hc56, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAB8_H_L_H_I (m : N8Model)
    (hb5 : CMSig2_8_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h6bigk := hb6.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  rcases m.htr 0 1 6 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 5 6 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 6 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 5 6 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 6 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 6 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 5 6 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 6 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 5 6 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 4 5 6 (by decide) (by decide) with h11 | h11
                        · rcases h6bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, hc16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, hc26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, h11, h9, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, h11, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h11, h6, h9, hc01, hc56, hlam, hphi, ht0b, ht6b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h1, h11, h9, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h1, h11, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h1, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h2, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h2, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h1, h11, h2, h9, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h1, h11, h2, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h1, h2, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h6, hc06, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h2, h6, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h6, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h11, h2, h6, hc01, hc56, hlam, hphi, ht0b, ht6b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h1, h2, h6, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p12_1, u5elo0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h7, hc06, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h2, h6, h9, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h7, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h9, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h2, h6, h9, hc01, hc56, hlam, hphi, ht0b, ht6b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h4, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h8, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h10, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h11, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                        · linarith only [h11, hc45, hlam, hphi, u5elo5]
                      · linarith only [h1, h10, hc35, hlam, hphi, u5elo0]
                    · linarith only [h0, h1, h2, h7, h9, hc34, hlam, hphi, ht45, u5elo0]
                  · linarith only [h1, h8, hc25, hlam, hphi, u5elo0]
                · rcases m.htr 2 5 6 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 3 4 6 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h1, h2, h54, h6, h7, hc24, hlam, hphi, ht45, u5elo0]
                    · rcases m.htr 3 5 6 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 4 5 6 (by decide) (by decide) with h57 | h57
                        · linarith only [h57, h7, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h3, h56, h57, hc45, hlam, hphi, u5elo1]
                      · linarith only [h56, hc35, hlam, hphi, u5elo5]
                  · linarith only [h1, h5, h53, hc35, hlam, hphi, u5elo0]
              · linarith only [h0, h1, h2, h5, h6, hc35, hlam, hphi, u5elo0]
            · linarith only [h5, hc23, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1, h4, hc15, hlam, hphi, u5elo0]
        · linarith only [h3, hc13, hlam, hphi, ht34, ht45, u5elo3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
        · rcases m.htr 1 5 6 (by decide) (by decide) with h67 | h67
          · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
            · rcases m.htr 2 3 6 (by decide) (by decide) with h69 | h69
              · rcases m.htr 2 4 6 (by decide) (by decide) with h70 | h70
                · rcases m.htr 2 5 6 (by decide) (by decide) with h71 | h71
                  · linarith only [h2, h71, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1, h71, hc25, hlam, hphi, u5elo0]
                · rcases m.htr 2 5 6 (by decide) (by decide) with h74 | h74
                  · linarith only [h2, h74, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1, h74, hc25, hlam, hphi, u5elo0]
              · rcases m.htr 2 4 6 (by decide) (by decide) with h77 | h77
                · rcases m.htr 2 5 6 (by decide) (by decide) with h78 | h78
                  · linarith only [h68, h69, h78, hc35, hlam, hphi, u5elo2]
                  · linarith only [h1, h78, hc25, hlam, hphi, u5elo0]
                · rcases m.htr 2 5 6 (by decide) (by decide) with h81 | h81
                  · linarith only [h2, h81, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1, h81, hc25, hlam, hphi, u5elo0]
            · linarith only [h68, hc23, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1, h67, hc15, hlam, hphi, u5elo0]
        · linarith only [h66, hc13, hlam, hphi, ht34, ht45, u5elo3]
    · linarith only [h1, hc05, hlam, hphi, u5elo5]
  · rcases m.htr 0 5 6 (by decide) (by decide) with h88 | h88
    · rcases m.htr 1 2 6 (by decide) (by decide) with h89 | h89
      · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
        · rcases m.htr 1 5 6 (by decide) (by decide) with h91 | h91
          · linarith only [h0, h91, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
          · linarith only [h91, hc15, hlam, hphi, u5elo5]
        · linarith only [h90, hc13, hlam, hphi, ht34, ht45, u5elo3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
        · rcases m.htr 1 5 6 (by decide) (by decide) with h96 | h96
          · linarith only [h0, h96, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
          · linarith only [h96, hc15, hlam, hphi, u5elo5]
        · linarith only [h95, hc13, hlam, hphi, ht34, ht45, u5elo3]
    · linarith only [h88, hc05, hlam, hphi, u5elo5]

theorem n8l_sAB8_H_L_H_L (m : N8Model)
    (hb5 : CMSig2_8_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5elo := hb5.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h10, h12, h6, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                          · linarith only [h12, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h11, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h10, h16, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h16, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h19, h6, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h23 | h23
                            · linarith only [h0, h21, h22, h23, h6, hc01, hc56, hlam, hphi, ht0b, ht6b]
                            · linarith only [h23, hc45, hlam, hphi, u5elo5]
                          · linarith only [h22, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h21, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                    · linarith only [h30, h6, h7, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                      · linarith only [h30, h32, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h1, h32, h34, h5, h6, h7, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · linarith only [h34, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h29, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h44 | h44
                            · linarith only [h38, h41, h43, h44, h6, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h44, hc45, hlam, hphi, u5elo5]
                          · linarith only [h43, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h42, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1, h38, h41, h5, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                    · linarith only [h38, h40, h6, hlam]
                  · linarith only [h38, h39, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h57 | h57
                            · linarith only [h1, h53, h56, h57, hc01, hc56, hlam, hphi, ht0b, ht6b]
                            · linarith only [h57, hc45, hlam, hphi, u5elo5]
                          · linarith only [h56, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h38, h54, h55, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1, h5, h52, h54, h6, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h66 | h66
                            · linarith only [h52, h53, h6, h63, h64, h65, h66, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h66, hc45, hlam, hphi, u5elo5]
                          · linarith only [h53, h6, h65, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h52, h53, h6, h63, h64, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                      · linarith only [h1, h5, h52, h6, h63, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                  · linarith only [h52, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
              · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                    · linarith only [h1, h5, h76, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                      · linarith only [h0, h5, h73, h78, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h82 | h82
                            · linarith only [h0, h73, h80, h81, h82, hc01, hc56, hlam, hphi, ht0b, ht6b]
                            · linarith only [h82, hc45, hlam, hphi, u5elo5]
                          · linarith only [h1, h5, h73, h80, h81, hc35, hlam, hphi, u5elo4]
                        · linarith only [h80, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h73, h75, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                    · linarith only [h1, h5, h89, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                      · linarith only [h2, h5, h73, h74, h91, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h95 | h95
                            · linarith only [h73, h74, h93, h94, h95, hc24, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h95, hc45, hlam, hphi, u5elo5]
                          · linarith only [h73, h74, h91, h94, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h93, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h73, h88, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                    · linarith only [h1, h103, h5, hlam]
                    · linarith only [h101, h103, h73, hlam]
                  · linarith only [h101, h102, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                    · linarith only [h1, h108, h5, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h113 | h113
                            · linarith only [h1, h107, h110, h111, h112, h113, h5, h73, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h113, hc45, hlam, hphi, u5elo5]
                          · linarith only [h1, h107, h111, h112, h5, h73, hc35, hlam, hphi, u5elo4]
                        · linarith only [h1, h107, h110, h111, h5, h73, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h120 | h120
                            · linarith only [h107, h110, h118, h119, h120, h73, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h120, hc45, hlam, hphi, u5elo5]
                          · linarith only [h110, h119, h73, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h107, h118, h73, hc25, hlam, hphi, u5elo3]
                  · linarith only [h107, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h128 | h128
        · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
          · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
            · linarith only [h1, h130, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
              · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                · linarith only [h0, h133, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                    · linarith only [h1, h130, h133, h136, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                    · linarith only [h0, h132, h136, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h132, h135, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                · linarith only [h1, h132, h140, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                    · linarith only [h1, h130, h143, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                      · linarith only [h1, h132, h142, h143, h145, h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h149 | h149
                            · linarith only [h1, h132, h140, h142, h145, h147, h148, h149, h2, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h149, hc45, hlam, hphi, u5elo5]
                          · linarith only [h1, h132, h140, h142, h145, h147, h148, h2, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b]
                        · linarith only [h147, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h142, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h129, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h128, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h157 | h157
      · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 3 4 (by decide) (by decide) with h160 | h160
            · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
              · linarith only [h0, h1, h161, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
                · rcases m.htr 1 2 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                          · linarith only [h0, h1, h161, h163, h166, h168, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                          · linarith only [h168, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h1, h161, h167, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h161, h163, h166, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                    · linarith only [h1, h157, h160, h165, hlam]
                  · linarith only [h163, h164, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h180 | h180
                            · linarith only [h0, h1, h161, h175, h178, h179, h180, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h180, hc45, hlam, hphi, u5elo5]
                          · linarith only [h179, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1, h157, h161, h163, h178, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h157, h161, h163, h175, h177, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                    · linarith only [h1, h157, h160, h176, hlam]
                  · linarith only [h175, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1, h157, h160, hlam]
          · linarith only [h159, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h158, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h191 | h191
        · rcases m.htr 0 2 5 (by decide) (by decide) with h192 | h192
          · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
            · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
              · linarith only [h0, h1, h194, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                · linarith only [h0, h157, h196, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h203 | h203
                            · linarith only [h0, h157, h194, h198, h199, h201, h202, h203, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h203, hc45, hlam, hphi, u5elo5]
                          · linarith only [h202, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h157, h194, h199, h201, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h157, h194, h198, h199, h200, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                    · linarith only [h0, h1, h198, h199, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                  · linarith only [h198, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
              · linarith only [h0, h1, h193, h211, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                · linarith only [h0, h157, h213, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
                    · linarith only [h0, h1, h193, h211, h215, h216, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                    · linarith only [h0, h1, h215, h216, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                  · linarith only [h215, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h192, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h191, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h222 | h222
    · rcases m.htr 0 1 4 (by decide) (by decide) with h223 | h223
      · rcases m.htr 0 1 5 (by decide) (by decide) with h224 | h224
        · rcases m.htr 0 2 5 (by decide) (by decide) with h225 | h225
          · rcases m.htr 0 3 4 (by decide) (by decide) with h226 | h226
            · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
              · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
                · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                          · linarith only [h0, h222, h227, h231, h233, hc12, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b]
                          · linarith only [h233, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h232, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h222, h230, h231, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                      · linarith only [h227, h230, h238, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                        · linarith only [h0, h222, h226, h227, h230, h240, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                        · linarith only [h240, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h229, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h223, h228, hlam]
              · linarith only [h0, h222, h227, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
              · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h249 | h249
                    · linarith only [h0, h222, h226, h249, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                      · linarith only [h222, h226, h246, h251, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h253 | h253
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h254 | h254
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h255 | h255
                            · linarith only [h0, h223, h246, h249, h253, h254, h255, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                            · linarith only [h255, hc45, hlam, hphi, u5elo5]
                          · linarith only [h226, h254, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h253, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h248, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h223, h247, hlam]
              · linarith only [h0, h222, h246, hlam]
          · linarith only [h0, h222, h225, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h222, h224, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h265 | h265
        · rcases m.htr 0 2 5 (by decide) (by decide) with h266 | h266
          · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
            · linarith only [h222, h223, h267, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
              · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                    · linarith only [h222, h223, h267, h270, h272, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                      · linarith only [h222, h223, h269, h272, h274, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h278 | h278
                            · linarith only [h222, h223, h269, h272, h276, h277, h278, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h278, hc45, hlam, hphi, u5elo5]
                          · linarith only [h222, h223, h272, h277, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h276, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h271, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h285 | h285
                    · linarith only [h0, h222, h270, h285, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
                      · linarith only [h0, h222, h269, h270, h285, h287, hlam]
                      · linarith only [h0, h222, h269, h270, h287, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h222, h269, h284, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h0, h222, h269, hlam]
          · linarith only [h0, h266, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h222, h265, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h294 | h294
      · rcases m.htr 0 1 5 (by decide) (by decide) with h295 | h295
        · rcases m.htr 0 2 5 (by decide) (by decide) with h296 | h296
          · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
            · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
              · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
                · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h305 | h305
                            · linarith only [h222, h294, h298, h299, h302, h304, h305, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                            · linarith only [h305, hc45, hlam, hphi, u5elo5]
                          · linarith only [h304, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h303, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                        · linarith only [h222, h294, h298, h301, h302, h310, hc12, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b]
                        · linarith only [h310, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h222, h294, h297, h301, hc03, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                  · linarith only [h222, h294, h296, h298, h299, h300, hc02, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                · linarith only [h222, h294, h298, h299, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
                · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h321 | h321
                          · linarith only [h0, h294, h298, h316, h319, h321, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                          · linarith only [h321, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h298, h320, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h294, h298, h316, h319, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                    · linarith only [h0, h294, h297, h298, h318, hlam]
                  · linarith only [h0, h294, h316, h317, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h294, h316, hlam]
            · linarith only [h222, h294, h297, hlam]
          · linarith only [h296, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h295, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h332 | h332
        · rcases m.htr 0 2 5 (by decide) (by decide) with h333 | h333
          · rcases m.htr 0 3 4 (by decide) (by decide) with h334 | h334
            · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
              · rcases m.htr 1 2 4 (by decide) (by decide) with h336 | h336
                · rcases m.htr 1 2 5 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h340 | h340
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h342 | h342
                            · linarith only [h335, h339, h341, h342, hc12, hc56, hlam, hphi, ht01, ht0b, ht6b]
                            · linarith only [h342, hc45, hlam, hphi, u5elo5]
                          · linarith only [h341, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h340, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h347 | h347
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h348 | h348
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h349 | h349
                            · linarith only [h334, h339, h347, h348, h349, hc03, hc56, hlam, hphi, ht0b, ht6b]
                            · linarith only [h349, hc45, hlam, hphi, u5elo5]
                          · linarith only [h339, h348, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h347, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h222, h334, h338, hlam]
                  · linarith only [h222, h334, h335, h337, hc34, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h356 | h356
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h357 | h357
                    · linarith only [h335, h336, h357, hlam]
                    · linarith only [h222, h332, h334, h357, hc03, hc15, hlam, hphi, ht0b, ht56, ht6b]
                  · linarith only [h222, h332, h335, h356, hc15, hlam, hphi, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
                · rcases m.htr 1 2 5 (by decide) (by decide) with h362 | h362
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h366 | h366
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h367 | h367
                            · linarith only [h294, h332, h335, h361, h362, h365, h366, h367, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h367, hc45, hlam, hphi, u5elo5]
                          · linarith only [h366, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h294, h335, h361, h365, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h294, h332, h335, h361, h362, h364, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                    · linarith only [h222, h334, h363, hlam]
                  · linarith only [h294, h332, h361, h362, hc15, hlam, hphi, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h378 | h378
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h380 | h380
                            · linarith only [h0, h332, h361, h375, h377, h378, h379, h380, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h380, hc45, hlam, hphi, u5elo5]
                          · linarith only [h379, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h361, h377, h378, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h332, h334, h335, h375, h377, hc03, hc25, hlam, hphi, ht0b, ht56, ht6b]
                    · linarith only [h222, h334, h376, hlam]
                  · linarith only [h0, h332, h375, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
              · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
                · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h392 | h392
                      · linarith only [h222, h332, h334, h388, h390, h392, hc12, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h394 | h394
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h395 | h395
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h396 | h396
                            · linarith only [h222, h332, h334, h390, h391, h394, h395, h396, hc13, hc56, hlam, hphi, ht01, ht0b, ht6b]
                            · linarith only [h396, hc45, hlam, hphi, u5elo5]
                          · linarith only [h222, h334, h395, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h394, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                      · linarith only [h222, h332, h390, h391, h401, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h403 | h403
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h404 | h404
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h405 | h405
                            · linarith only [h222, h332, h390, h391, h403, h404, h405, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h405, hc45, hlam, hphi, u5elo5]
                          · linarith only [h222, h391, h404, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h403, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h390, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
                    · linarith only [h222, h332, h334, h388, h389, h411, h412, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                      · linarith only [h222, h332, h411, h412, h414, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h417 | h417
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h418 | h418
                            · linarith only [h0, h332, h389, h411, h414, h416, h417, h418, hc34, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h418, hc45, hlam, hphi, u5elo5]
                          · linarith only [h222, h388, h389, h414, h417, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h416, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h222, h332, h388, h411, hc15, hlam, hphi, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h424 | h424
                · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
                      · linarith only [h222, h332, h334, h388, h424, h425, h427, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                      · linarith only [h388, h424, h426, h427, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                    · linarith only [h388, h424, h426, hlam]
                  · linarith only [h425, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h436 | h436
                          · rcases m.htr 4 5 6 (by decide) (by decide) with h437 | h437
                            · linarith only [h222, h332, h334, h388, h432, h433, h435, h436, h437, hc23, hc56, hlam, hphi, ht01, ht0b, ht12, ht6b]
                            · linarith only [h437, hc45, hlam, hphi, u5elo5]
                          · linarith only [h222, h334, h436, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h222, h332, h334, h388, h432, h433, h435, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                      · linarith only [h388, h433, h434, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h443 | h443
                      · linarith only [h222, h332, h432, h433, h443, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                      · linarith only [h0, h332, h388, h432, h443, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                  · linarith only [h0, h332, h432, hc15, hlam, hphi, u5elo2]
          · linarith only [h333, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h332, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n8l_sAB8_H_R_H_R (m : N8Model)
    (hb5 : CMSig2_8_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.1
  have h6ehi := hb6.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 5 6 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h12, h7, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h14 | h14
                          · linarith only [h14, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                          · linarith only [h14, hc56, hlam, hphi, u5ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                        · linarith only [h11, h17, h8, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h19 | h19
                          · linarith only [h19, h3, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h19, hc56, hlam, hphi, u5ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h22, h5, h8, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h24, h7, h8, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h26, h5, h7, h8, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h28 | h28
                          · linarith only [h28, h3, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h28, hc56, hlam, hphi, u5ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h32, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h1, h35, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h37 | h37
                          · linarith only [h3, h37, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h37, hc56, hlam, hphi, u5ehi1]
                      · linarith only [h31, h34, h7, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h0, h4, h41, h7, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h1, h44, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h46 | h46
                          · linarith only [h3, h46, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h46, hc56, hlam, hphi, u5ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h43, h49, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h51 | h51
                          · linarith only [h3, h51, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h51, hc56, hlam, hphi, u5ehi1]
              · linarith only [h6, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h55 | h55
              · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
                · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                  · linarith only [h0, h5, h57, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h0, h5, h59, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                      · linarith only [h56, h57, h61, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h56, h59, h63, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h65 | h65
                          · linarith only [h3, h65, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h55, h65, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi1]
                · linarith only [h4, h5, h56, hc12, hc24, hlam, hphi]
              · linarith only [h55, hc56, hlam, hphi, u5ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h70 | h70
            · rcases m.htr 0 5 6 (by decide) (by decide) with h71 | h71
              · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                · linarith only [h0, h4, h70, h72, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                    · linarith only [h0, h75, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h1, h78, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h80 | h80
                          · linarith only [h3, h80, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h71, h80, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi1]
                      · linarith only [h72, h74, h77, hlam]
                  · linarith only [h4, h70, h74, hc12, hc23, hlam, hphi]
              · linarith only [h71, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h4, h87, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                  · linarith only [h0, h70, h89, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
                    · linarith only [h0, h4, h91, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h1, h94, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h96 | h96
                          · linarith only [h3, h96, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h86, h96, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                        · linarith only [h93, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h101 | h101
                          · linarith only [h101, h3, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h101, hc56, hlam, hphi, u5ehi1]
              · linarith only [h86, hc56, hlam, hphi, u5ehi0]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h105 | h105
          · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
            · rcases m.htr 0 5 6 (by decide) (by decide) with h107 | h107
              · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
                    · linarith only [h0, h110, h3, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h0, h108, h110, h113, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · linarith only [h0, h108, h113, h3, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h0, h109, h110, h112, h116, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · linarith only [h0, h108, h116, h3, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h106, h108, h109, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h105, h108, h120, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                    · linarith only [h0, h105, h108, h122, h3, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                    · linarith only [h0, h105, h108, h122, h3, hc12, hc25, hlam, hphi]
              · linarith only [h107, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h126 | h126
              · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h106, h128, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                    · linarith only [h128, h130, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                      · linarith only [h127, h128, h132, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                        · linarith only [h127, h128, h130, h134, h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · linarith only [h127, h128, h134, h2, h3, hc23, hc35, hlam, hphi]
                · linarith only [h105, h106, h127, hc12, hc24, hlam, hphi]
              · linarith only [h126, hc56, hlam, hphi, u5ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 0 5 6 (by decide) (by decide) with h140 | h140
              · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
                · linarith only [h0, h105, h141, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                    · linarith only [h0, h105, h144, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                        · linarith only [h1, h144, h147, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h149 | h149
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h151 | h151
                              · linarith only [h1, h141, h143, h147, h150, h151, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h153 | h153
                                · linarith only [h151, h153, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h155 | h155
                                  · linarith only [h1, h141, h143, h144, h151, h155, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi4]
                                  · linarith only [h1, h141, h143, h144, h150, h155, h3, hc34, hc45, hlam, hphi]
                            · linarith only [h1, h105, h146, h150, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                          · linarith only [h1, h140, h141, h149, h3, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                      · linarith only [h141, h143, h146, hlam]
                  · linarith only [h105, h139, h143, hc12, hc23, hlam, hphi]
              · linarith only [h140, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h163 | h163
              · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
                · linarith only [h0, h105, h164, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                  · linarith only [h0, h139, h166, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                    · linarith only [h0, h105, h168, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h1, h168, h171, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h173 | h173
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                              · linarith only [h1, h170, h171, h175, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h177 | h177
                                · linarith only [h175, h177, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                                  · linarith only [h174, h175, h179, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi4]
                                  · linarith only [h1, h168, h170, h179, h3, hc34, hc45, hlam, hphi]
                            · linarith only [h1, h170, h174, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                          · linarith only [h1, h163, h166, h170, h173, h3, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                        · linarith only [h170, h184, h2, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h186 | h186
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                              · linarith only [h163, h184, h188, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                              · linarith only [h164, h170, h187, h188, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                              · linarith only [h163, h184, h191, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h193 | h193
                                · linarith only [h187, h193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h196 | h196
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h197 | h197
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h198 | h198
                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h199 | h199
                                          · linarith only [h195, h199, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                                          · linarith only [h163, h199, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                        · linarith only [h163, h168, h191, h198, h3, hlam]
                                      · linarith only [h0, h105, h187, h197, hc12, hc45, hlam, hphi, ht23, ht34]
                                    · linarith only [h163, h168, h196, h3, hlam]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h205 | h205
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                                      · linarith only [h0, h139, h195, h206, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h0, h105, h187, h206, hc12, hc45, hlam, hphi, ht23, ht34]
                                    · linarith only [h163, h168, h205, h3, hlam]
                          · linarith only [h163, h186, h3, hlam]
              · linarith only [h163, hc56, hlam, hphi, u5ehi0]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
        · linarith only [h2, h212, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h214 | h214
          · rcases m.htr 0 2 4 (by decide) (by decide) with h215 | h215
            · linarith only [h0, h2, h215, hlam]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h217 | h217
              · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                  · linarith only [h0, h2, h215, h219, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                    · linarith only [h0, h2, h219, h221, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                      · linarith only [h0, h1, h2, h214, h223, hlam]
                      · linarith only [h0, h2, h218, h223, hc23, hc34, hlam, hphi]
                · linarith only [h214, h215, h218, hc12, hc24, hlam, hphi]
              · linarith only [h217, hc56, hlam, hphi, u5ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h228 | h228
            · linarith only [h0, h2, h228, hlam]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h230 | h230
              · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
                · linarith only [h0, h212, h214, h231, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                  · linarith only [h0, h2, h228, h233, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                    · linarith only [h1, h231, h235, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
                      · linarith only [h1, h2, h237, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h239 | h239
                        · linarith only [h1, h2, h237, h239, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h241 | h241
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                            · linarith only [h1, h2, h231, h237, h242, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                              · linarith only [h239, h242, h244, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h246 | h246
                                · linarith only [h242, h246, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h249 | h249
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h251 | h251
                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h252 | h252
                                          · linarith only [h248, h252, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                                          · linarith only [h230, h252, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                        · linarith only [h212, h230, h235, h244, h251, hlam]
                                      · linarith only [h1, h2, h231, h233, h242, h250, hc12, hc45, hlam, hphi, ht23, ht34]
                                    · linarith only [h212, h230, h235, h249, hlam]
                                  · linarith only [h1, h2, h231, h233, h248, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h212, h230, h241, hlam]
              · linarith only [h230, hc56, hlam, hphi, u5ehi0]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h261 | h261
      · rcases m.htr 0 1 5 (by decide) (by decide) with h262 | h262
        · linarith only [h1, h262, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h264 | h264
          · linarith only [h0, h1, h264, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h266 | h266
            · rcases m.htr 0 5 6 (by decide) (by decide) with h267 | h267
              · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                · linarith only [h0, h1, h264, h268, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                    · linarith only [h0, h1, h268, h271, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h275 | h275
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h278 | h278
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                                  · linarith only [h0, h262, h268, h270, h274, h279, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi4]
                                  · linarith only [h0, h262, h270, h271, h279, hc24, hc45, hlam, hphi]
                                · linarith only [h0, h262, h268, h270, h274, h276, h278, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                              · linarith only [h268, h274, h277, hlam]
                            · linarith only [h0, h262, h268, h270, h274, h276, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                          · linarith only [h0, h262, h267, h270, h275, hc05, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h0, h1, h270, h274, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                      · linarith only [h0, h1, h270, h273, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                  · linarith only [h0, h1, h266, h268, h270, hc12, hc23, hlam, hphi]
              · linarith only [h267, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h290 | h290
              · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                · linarith only [h0, h1, h264, h291, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                  · linarith only [h0, h1, h266, h291, h293, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
                    · linarith only [h0, h1, h291, h295, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h298 | h298
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h299 | h299
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h302 | h302
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h304 | h304
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                                      · linarith only [h261, h262, h295, h297, h300, h303, h305, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi4]
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h307 | h307
                                        · linarith only [h298, h307, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                        · linarith only [h290, h307, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                                    · linarith only [h262, h290, h295, h304, hlam]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h311 | h311
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h312 | h312
                                      · linarith only [h261, h262, h295, h297, h303, h312, hlam]
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h314 | h314
                                        · linarith only [h298, h314, hc13, hlam, hphi, ht01, ht0b, ht6b, u6ehi5]
                                        · linarith only [h314, hc56, hlam, hphi, u5ehi3]
                                    · linarith only [h262, h290, h295, h311, hlam]
                                · linarith only [h1, h261, h291, h293, h302, hc12, hc36, hlam, hphi, ht23]
                              · linarith only [h262, h290, h291, h298, h301, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                            · linarith only [h261, h262, h290, h291, h297, h298, h300, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                          · linarith only [h261, h262, h290, h299, hc05, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · linarith only [h1, h261, h293, h298, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h261, h293, h297, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h290, hc56, hlam, hphi, u5ehi0]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
        · linarith only [h1, h325, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h327 | h327
          · linarith only [h0, h1, h327, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
            · linarith only [h0, h261, h329, hlam]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h331 | h331
              · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                · linarith only [h0, h1, h327, h332, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                  · linarith only [h0, h261, h329, h334, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
                    · linarith only [h0, h1, h332, h336, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h339 | h339
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h340 | h340
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h343 | h343
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h345 | h345
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h346 | h346
                                      · linarith only [h332, h338, h346, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi4]
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h348 | h348
                                        · linarith only [h341, h344, h346, h348, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                                        · linarith only [h331, h348, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                                    · linarith only [h325, h331, h336, h345, hlam]
                                  · linarith only [h0, h261, h334, h344, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h332, h343, hc12, hc36, hlam, hphi, ht23]
                              · linarith only [h325, h331, h332, h339, h342, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                            · linarith only [h325, h331, h332, h339, h341, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                          · linarith only [h325, h331, h340, hlam]
                        · linarith only [h0, h1, h339, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h338, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h331, hc56, hlam, hphi, u5ehi0]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h360 | h360
    · rcases m.htr 0 1 4 (by decide) (by decide) with h361 | h361
      · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
        · linarith only [h0, h362, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h364 | h364
          · rcases m.htr 0 2 4 (by decide) (by decide) with h365 | h365
            · rcases m.htr 0 5 6 (by decide) (by decide) with h366 | h366
              · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                · rcases m.htr 1 2 4 (by decide) (by decide) with h368 | h368
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h371 | h371
                        · linarith only [h360, h362, h369, h371, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h373 | h373
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h374 | h374
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h375 | h375
                              · linarith only [h360, h362, h367, h371, h375, hlam]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h377 | h377
                                · linarith only [h360, h362, h367, h371, h377, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h379 | h379
                                  · linarith only [h360, h362, h368, h370, h371, h379, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h381 | h381
                                    · linarith only [h369, h381, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h366, h381, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                            · linarith only [h360, h362, h370, h371, h374, hc23, hc35, hlam, hphi]
                          · linarith only [h362, h366, h373, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                        · linarith only [h370, h386, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h388 | h388
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                            · linarith only [h360, h362, h364, h370, h386, h389, hc13, hc35, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h391 | h391
                              · linarith only [h362, h367, h370, h386, h391, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h393 | h393
                                · linarith only [h361, h367, h370, h393, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
                                  · linarith only [h365, h395, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h397 | h397
                                    · linarith only [h369, h397, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h366, h397, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                          · linarith only [h362, h366, h388, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                      · linarith only [h0, h360, h369, h401, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
                        · linarith only [h0, h361, h369, h401, h403, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h405 | h405
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h406 | h406
                            · linarith only [h367, h401, h406, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                              · linarith only [h0, h361, h362, h367, h369, h401, h403, h408, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi0]
                              · linarith only [h0, h361, h367, h369, h401, h408, hc23, hc35, hlam, hphi]
                          · linarith only [h362, h366, h405, hlam]
                  · linarith only [h0, h365, h368, hlam]
                · linarith only [h0, h364, h367, hlam]
              · linarith only [h366, hc56, hlam, hphi, u5ehi0]
            · linarith only [h0, h361, h365, hlam]
          · linarith only [h0, h360, h364, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h417 | h417
        · linarith only [h0, h417, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h419 | h419
          · rcases m.htr 0 2 4 (by decide) (by decide) with h420 | h420
            · rcases m.htr 0 5 6 (by decide) (by decide) with h421 | h421
              · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h424 | h424
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
                      · linarith only [h360, h361, h425, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h427 | h427
                        · linarith only [h360, h361, h425, h427, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h429 | h429
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                            · linarith only [h360, h361, h422, h425, h430, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                              · linarith only [h360, h417, h422, h427, h432, hlam]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h434 | h434
                                · linarith only [h360, h361, h422, h425, h434, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h436 | h436
                                  · linarith only [h420, h436, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h438 | h438
                                    · linarith only [h424, h438, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h421, h438, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                          · linarith only [h417, h421, h429, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                      · linarith only [h360, h361, h423, h424, h442, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h444 | h444
                        · linarith only [h360, h361, h423, h424, h444, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h446 | h446
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                            · linarith only [h360, h361, h422, h442, h447, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                              · linarith only [h360, h361, h417, h421, h422, h423, h424, h444, h449, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                              · linarith only [h360, h361, h422, h423, h424, h449, hc23, hc35, hlam, hphi]
                          · linarith only [h417, h421, h446, hlam]
                  · linarith only [h0, h420, h423, hlam]
                · linarith only [h0, h419, h422, hlam]
              · linarith only [h421, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h456 | h456
              · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                · rcases m.htr 1 2 4 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                      · linarith only [h0, h360, h420, h458, h460, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h462 | h462
                        · linarith only [h0, h360, h420, h458, h462, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h464 | h464
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h465 | h465
                            · linarith only [h0, h360, h420, h457, h458, h460, h465, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h467 | h467
                              · linarith only [h0, h360, h417, h420, h456, h457, h458, h462, h467, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h469 | h469
                                · linarith only [h0, h360, h420, h457, h458, h469, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h471 | h471
                                  · linarith only [h458, h471, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · linarith only [h0, h360, h420, h471, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h417, h456, h464, hlam]
                    · linarith only [h0, h360, h420, h457, h458, h459, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h476 | h476
                    · linarith only [h458, h476, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h478 | h478
                      · linarith only [h0, h360, h458, h478, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
                        · linarith only [h0, h360, h458, h480, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h482 | h482
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                            · linarith only [h0, h360, h417, h419, h420, h456, h458, h478, h480, h483, hc04, hc13, hc35, hlam, hphi, ht0b, ht56, ht6b, u5ehi5]
                            · linarith only [h0, h360, h457, h458, h483, hc23, hc34, hlam, hphi]
                          · linarith only [h417, h456, h482, hlam]
                · linarith only [h0, h419, h457, hlam]
              · linarith only [h456, hc56, hlam, hphi, u5ehi0]
          · linarith only [h0, h360, h419, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h490 | h490
      · rcases m.htr 0 1 5 (by decide) (by decide) with h491 | h491
        · linarith only [h360, h491, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h493 | h493
          · rcases m.htr 0 2 4 (by decide) (by decide) with h494 | h494
            · rcases m.htr 0 5 6 (by decide) (by decide) with h495 | h495
              · rcases m.htr 1 2 3 (by decide) (by decide) with h496 | h496
                · rcases m.htr 1 2 4 (by decide) (by decide) with h497 | h497
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h499 | h499
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h500 | h500
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h501 | h501
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h502 | h502
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h503 | h503
                              · linarith only [h493, h503, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h505 | h505
                                · linarith only [h496, h500, h503, h505, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h507 | h507
                                  · linarith only [h490, h491, h496, h497, h500, h507, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h509 | h509
                                    · linarith only [h496, h500, h503, h509, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h495, h509, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                              · linarith only [h490, h491, h496, h499, h500, h502, h512, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h514 | h514
                                · linarith only [h490, h491, h496, h499, h500, h502, h514, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h516 | h516
                                  · linarith only [h490, h491, h496, h499, h500, h502, h516, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h518 | h518
                                    · linarith only [h498, h518, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h518, hc56, hlam, hphi, u5ehi2]
                          · linarith only [h491, h495, h501, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h522 | h522
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                              · linarith only [h360, h490, h497, h500, h523, h524, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h526 | h526
                                · linarith only [h493, h526, hc02, hlam, hphi, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h528 | h528
                                  · linarith only [h360, h490, h497, h500, h528, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h530 | h530
                                    · linarith only [h498, h530, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h530, hc56, hlam, hphi, u5ehi2]
                            · linarith only [h499, h500, h523, hc23, hc35, hlam, hphi]
                          · linarith only [h491, h495, h522, hlam]
                      · linarith only [h360, h490, h499, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h537 | h537
                        · linarith only [h496, h498, h537, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h539 | h539
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h541 | h541
                              · linarith only [h491, h493, h537, h541, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi0]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h543 | h543
                                · linarith only [h0, h493, h498, h541, h543, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h545 | h545
                                  · linarith only [h490, h497, h545, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · linarith only [h360, h490, h496, h498, h545, hc14, hc45, hlam, hphi]
                            · linarith only [h360, h490, h496, h498, h536, h540, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                          · linarith only [h491, h495, h539, hlam]
                      · linarith only [h360, h490, h536, hlam]
                  · linarith only [h0, h494, h497, hlam]
                · linarith only [h0, h493, h496, hlam]
              · linarith only [h495, hc56, hlam, hphi, u5ehi0]
            · linarith only [h0, h490, h494, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h555 | h555
            · rcases m.htr 0 5 6 (by decide) (by decide) with h556 | h556
              · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                · rcases m.htr 1 2 4 (by decide) (by decide) with h558 | h558
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h559 | h559
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h561 | h561
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h562 | h562
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h564 | h564
                              · linarith only [h557, h564, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                              · linarith only [h0, h490, h493, h558, h561, h563, h564, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                            · linarith only [h0, h490, h493, h557, h558, h560, h563, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                          · linarith only [h491, h556, h562, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h569 | h569
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h570 | h570
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h571 | h571
                              · linarith only [h360, h490, h558, h561, h570, h571, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h573 | h573
                                · linarith only [h557, h561, h573, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h575 | h575
                                  · linarith only [h490, h558, h575, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h577 | h577
                                    · linarith only [h559, h577, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h556, h577, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                            · linarith only [h0, h493, h560, h561, h570, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h491, h556, h569, hlam]
                      · linarith only [h360, h490, h560, hlam]
                    · linarith only [h0, h490, h493, h557, h558, h559, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                  · linarith only [h0, h490, h493, h557, h558, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h586 | h586
                    · linarith only [h557, h586, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h589 | h589
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h590 | h590
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h592 | h592
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h593 | h593
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
                                  · linarith only [h490, h585, h594, hc01, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · linarith only [h0, h490, h586, h594, hc14, hc45, hlam, hphi]
                                · linarith only [h0, h490, h557, h585, h591, h593, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                              · linarith only [h491, h556, h557, h589, h592, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi5]
                            · linarith only [h491, h556, h557, h589, h591, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                          · linarith only [h491, h556, h590, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h601 | h601
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h602 | h602
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h603 | h603
                              · linarith only [h0, h557, h589, h603, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h490, h557, h585, h602, h603, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                            · linarith only [h0, h490, h557, h585, h602, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                          · linarith only [h491, h556, h601, hlam]
                      · linarith only [h0, h490, h557, h588, hlam]
                  · linarith only [h0, h555, h585, hlam]
              · linarith only [h556, hc56, hlam, hphi, u5ehi0]
            · linarith only [h0, h490, h555, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h612 | h612
        · linarith only [h0, h612, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h614 | h614
          · rcases m.htr 0 2 4 (by decide) (by decide) with h615 | h615
            · rcases m.htr 0 5 6 (by decide) (by decide) with h616 | h616
              · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
                · rcases m.htr 1 2 4 (by decide) (by decide) with h618 | h618
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h619 | h619
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h620 | h620
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h621 | h621
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h622 | h622
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h623 | h623
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h624 | h624
                              · linarith only [h614, h624, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h626 | h626
                                · linarith only [h617, h621, h624, h626, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h628 | h628
                                  · linarith only [h617, h621, h623, h624, h628, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h630 | h630
                                    · linarith only [h617, h621, h624, h630, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h616, h630, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
                              · linarith only [h623, h633, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h635 | h635
                                · linarith only [h617, h620, h623, h635, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h637 | h637
                                  · linarith only [h615, h637, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h639 | h639
                                    · linarith only [h619, h639, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h639, hc56, hlam, hphi, u5ehi2]
                          · linarith only [h612, h616, h622, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h643 | h643
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h644 | h644
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
                              · linarith only [h490, h620, h621, h645, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h647 | h647
                                · linarith only [h360, h614, h621, h647, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h649 | h649
                                  · linarith only [h0, h615, h649, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h651 | h651
                                    · linarith only [h619, h651, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h616, h651, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                            · linarith only [h620, h621, h644, hc23, hc35, hlam, hphi]
                          · linarith only [h612, h616, h643, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h656 | h656
                        · linarith only [h620, h656, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h658 | h658
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
                            · linarith only [h360, h620, h659, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h661 | h661
                              · linarith only [h360, h612, h614, h620, h656, h661, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h663 | h663
                                · linarith only [h360, h614, h620, h663, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h665 | h665
                                  · linarith only [h0, h615, h665, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h667 | h667
                                    · linarith only [h619, h667, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h616, h667, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                          · linarith only [h612, h616, h658, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h671 | h671
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h672 | h672
                        · linarith only [h617, h619, h672, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h674 | h674
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h675 | h675
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h676 | h676
                              · linarith only [h0, h614, h619, h672, h676, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h678 | h678
                                · linarith only [h0, h614, h619, h676, h678, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                                  · linarith only [h0, h614, h619, h675, h676, h680, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi4]
                                  · linarith only [h0, h614, h619, h675, h680, hc34, hc45, hlam, hphi]
                            · linarith only [h671, h672, h675, hc23, hc35, hlam, hphi]
                          · linarith only [h612, h616, h674, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h685 | h685
                        · linarith only [h671, h685, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h687 | h687
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h688 | h688
                            · linarith only [h0, h612, h614, h616, h619, h671, h685, h688, hc13, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h690 | h690
                              · linarith only [h0, h612, h615, h616, h619, h685, h688, h690, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h692 | h692
                                · linarith only [h0, h615, h619, h688, h690, h692, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h694 | h694
                                  · linarith only [h0, h615, h619, h690, h694, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h696 | h696
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h697 | h697
                                      · linarith only [h0, h615, h619, h688, h694, h697, hc23, hc34, hlam, hphi]
                                      · linarith only [h360, h671, h697, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                    · linarith only [h612, h616, h619, h696, hlam]
                          · linarith only [h612, h616, h687, hlam]
                  · linarith only [h0, h615, h618, hlam]
                · linarith only [h0, h614, h617, hlam]
              · linarith only [h616, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h705 | h705
              · rcases m.htr 1 2 3 (by decide) (by decide) with h706 | h706
                · rcases m.htr 1 2 4 (by decide) (by decide) with h707 | h707
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h709 | h709
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h710 | h710
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h711 | h711
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                            · linarith only [h614, h615, h707, h712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                              · linarith only [h614, h615, h706, h709, h712, h714, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h716 | h716
                                · linarith only [h614, h615, h706, h709, h712, h716, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h718 | h718
                                  · linarith only [h706, h709, h712, h718, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · linarith only [h614, h615, h718, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h612, h705, h711, hlam]
                        · linarith only [h614, h615, h707, h709, h710, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                        · linarith only [h709, h723, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h725 | h725
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h726 | h726
                            · linarith only [h614, h615, h707, h709, h726, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h728 | h728
                              · linarith only [h612, h614, h615, h705, h707, h723, h728, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h730 | h730
                                · linarith only [h614, h615, h707, h730, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h732 | h732
                                  · linarith only [h707, h732, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · linarith only [h614, h615, h732, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h612, h705, h725, hlam]
                    · linarith only [h614, h615, h707, h708, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                    · linarith only [h707, h737, hc24, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h739 | h739
                      · linarith only [h706, h707, h739, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h741 | h741
                        · linarith only [h739, h741, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h743 | h743
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h744 | h744
                            · linarith only [h0, h360, h614, h707, h739, h744, hc01, hc14, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h746 | h746
                              · linarith only [h0, h612, h614, h705, h707, h741, h744, h746, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h748 | h748
                                · linarith only [h0, h614, h707, h744, h748, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h750 | h750
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h751 | h751
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h752 | h752
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h753 | h753
                                        · rcases m.htr 4 5 6 (by decide) (by decide) with h754 | h754
                                          · linarith only [h744, h750, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                                          · linarith only [h705, h754, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                        · linarith only [h612, h705, h737, h746, h753, hlam]
                                      · linarith only [h0, h614, h737, h744, h750, h752, hc23, hc45, hlam, hphi, ht34]
                                    · linarith only [h612, h705, h737, h751, hlam]
                                  · linarith only [h614, h615, h750, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h612, h705, h743, hlam]
                · linarith only [h0, h614, h706, hlam]
              · linarith only [h705, hc56, hlam, hphi, u5ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h764 | h764
            · rcases m.htr 0 5 6 (by decide) (by decide) with h765 | h765
              · rcases m.htr 1 2 3 (by decide) (by decide) with h766 | h766
                · rcases m.htr 1 2 4 (by decide) (by decide) with h767 | h767
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h768 | h768
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h769 | h769
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h770 | h770
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h771 | h771
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h772 | h772
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
                              · linarith only [h766, h773, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                              · linarith only [h614, h764, h770, h772, h773, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                            · linarith only [h614, h764, h766, h769, h772, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                          · linarith only [h612, h765, h771, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h778 | h778
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h779 | h779
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h780 | h780
                              · linarith only [h360, h770, h780, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h782 | h782
                                · linarith only [h766, h770, h782, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h784 | h784
                                  · linarith only [h764, h784, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h786 | h786
                                    · linarith only [h768, h786, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h765, h786, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                            · linarith only [h614, h769, h770, h779, hc02, hc35, hlam, hphi, ht23]
                          · linarith only [h612, h765, h778, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
                        · linarith only [h769, h791, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h793 | h793
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h794 | h794
                            · linarith only [h360, h769, h794, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h614, h764, h794, hlam]
                          · linarith only [h612, h765, h793, hlam]
                    · linarith only [h614, h764, h766, h768, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                  · linarith only [h614, h764, h766, h767, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h801 | h801
                    · linarith only [h766, h801, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h804 | h804
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h805 | h805
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h807 | h807
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h808 | h808
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h809 | h809
                                  · linarith only [h764, h809, hc02, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h811 | h811
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h812 | h812
                                      · linarith only [h612, h765, h801, h809, h812, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi5]
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h814 | h814
                                        · linarith only [h766, h804, h814, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi5]
                                        · linarith only [h612, h765, h801, h809, h814, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi3]
                                    · linarith only [h612, h765, h801, h811, hlam]
                                · linarith only [h490, h766, h800, h808, hc01, hc36, hlam, hphi, ht12, ht23]
                              · linarith only [h612, h765, h766, h804, h807, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi5]
                            · linarith only [h612, h765, h766, h804, h806, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                          · linarith only [h612, h765, h805, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h822 | h822
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h823 | h823
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h824 | h824
                              · linarith only [h360, h804, h824, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h490, h766, h800, h824, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h490, h766, h800, h823, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h612, h765, h822, hlam]
                      · linarith only [h766, h800, h803, hlam]
                  · linarith only [h0, h764, h800, hlam]
              · linarith only [h765, hc56, hlam, hphi, u5ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h832 | h832
              · rcases m.htr 1 2 3 (by decide) (by decide) with h833 | h833
                · rcases m.htr 1 2 4 (by decide) (by decide) with h834 | h834
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h835 | h835
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h836 | h836
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h837 | h837
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h838 | h838
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h840 | h840
                              · linarith only [h833, h840, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                              · linarith only [h0, h614, h837, h840, hc01, hc13, hlam, hphi]
                            · linarith only [h0, h614, h833, h836, h839, hc01, hc12, hlam, hphi]
                          · linarith only [h612, h832, h838, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h845 | h845
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h846 | h846
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h847 | h847
                              · linarith only [h833, h847, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h849 | h849
                                · linarith only [h833, h837, h849, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h851 | h851
                                  · linarith only [h834, h851, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h853 | h853
                                    · linarith only [h835, h853, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h832, h853, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                            · linarith only [h836, h837, h846, hc23, hc35, hlam, hphi]
                          · linarith only [h612, h832, h845, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h858 | h858
                        · linarith only [h836, h858, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h860 | h860
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h861 | h861
                            · linarith only [h360, h836, h861, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h863 | h863
                              · linarith only [h612, h833, h836, h858, h863, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h865 | h865
                                · linarith only [h833, h836, h865, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h867 | h867
                                  · linarith only [h834, h867, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h869 | h869
                                    · linarith only [h835, h869, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                                    · linarith only [h832, h869, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi2]
                          · linarith only [h612, h832, h860, hlam]
                    · linarith only [h0, h614, h833, h835, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h614, h833, h834, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h875 | h875
                  · linarith only [h0, h764, h833, h875, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h877 | h877
                    · linarith only [h833, h877, hc23, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h879 | h879
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h881 | h881
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h882 | h882
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h883 | h883
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h884 | h884
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h885 | h885
                                  · rcases m.htr 2 5 6 (by decide) (by decide) with h886 | h886
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h887 | h887
                                      · linarith only [h879, h887, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                                      · rcases m.htr 3 5 6 (by decide) (by decide) with h889 | h889
                                        · linarith only [h833, h880, h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi5]
                                        · linarith only [h889, hc56, hlam, hphi, u5ehi3]
                                    · linarith only [h612, h832, h877, h886, hlam]
                                  · linarith only [h0, h875, h885, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h833, h884, hc01, hc36, hlam, hphi, ht12, ht23]
                              · linarith only [h612, h832, h833, h880, h883, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                            · linarith only [h612, h832, h833, h880, h882, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                          · linarith only [h612, h832, h881, hlam]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h898 | h898
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h899 | h899
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h900 | h900
                              · linarith only [h360, h880, h900, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h833, h900, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h833, h879, h899, hc01, hc13, hlam, hphi]
                          · linarith only [h612, h832, h898, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h905 | h905
                        · linarith only [h879, h905, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
                        · rcases m.htr 1 5 6 (by decide) (by decide) with h907 | h907
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h908 | h908
                            · linarith only [h360, h879, h908, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h833, h908, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h612, h832, h907, hlam]
              · linarith only [h832, hc56, hlam, hphi, u5ehi0]

theorem n8l_sAB8_H_R_M_IR (m : N8Model)
    (hb5 : CMSig2_8_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
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
  have h5ehi := hb5.1
  have h6emax := hb6.2.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  rcases m.htr 0 5 6 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 6 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 5 6 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 5 6 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 6 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 5 6 (by decide) (by decide) with h7 | h7
                · linarith only [h1, h7, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                · linarith only [h0, h7, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
              · linarith only [h5, h6, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi4]
            · rcases m.htr 3 4 6 (by decide) (by decide) with h11 | h11
              · rcases m.htr 3 5 6 (by decide) (by decide) with h12 | h12
                · linarith only [h1, h12, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                · linarith only [h12, hc56, hlam, hphi, u5ehi3]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi5]
                · linarith only [h15, hc56, hlam, hphi, u5ehi3]
          · linarith only [h1, h3, h4, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
        · linarith only [h3, hc56, hlam, hphi, u5ehi1]
      · linarith only [h1, h2, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi3]
    · rcases m.htr 1 3 6 (by decide) (by decide) with h21 | h21
      · rcases m.htr 1 5 6 (by decide) (by decide) with h22 | h22
        · rcases m.htr 2 5 6 (by decide) (by decide) with h23 | h23
          · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
            · rcases m.htr 3 4 6 (by decide) (by decide) with h25 | h25
              · rcases m.htr 3 5 6 (by decide) (by decide) with h26 | h26
                · linarith only [h1, h21, h24, h26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                · linarith only [h1, h26, hc56, hlam, hphi, u5ehi1]
              · linarith only [h1, h21, h22, h24, h25, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi5]
            · rcases m.htr 3 4 6 (by decide) (by decide) with h30 | h30
              · rcases m.htr 3 5 6 (by decide) (by decide) with h31 | h31
                · linarith only [h1, h21, h31, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                · linarith only [h22, h31, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi3]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h34 | h34
                · linarith only [h1, h21, h24, h34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi5]
                · linarith only [h1, h34, hc56, hlam, hphi, u5ehi1]
          · linarith only [h23, hc56, hlam, hphi, u5ehi2]
        · linarith only [h0, h22, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi1]
      · rcases m.htr 1 5 6 (by decide) (by decide) with h39 | h39
        · rcases m.htr 2 5 6 (by decide) (by decide) with h40 | h40
          · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
            · rcases m.htr 3 4 6 (by decide) (by decide) with h42 | h42
              · rcases m.htr 3 5 6 (by decide) (by decide) with h43 | h43
                · rcases m.htr 4 5 6 (by decide) (by decide) with h44 | h44
                  · linarith only [h41, h44, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                  · linarith only [h40, h44, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi4]
                · linarith only [h1, h39, h43, hlam]
              · linarith only [h1, h39, h41, h42, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi5]
            · rcases m.htr 3 4 6 (by decide) (by decide) with h49 | h49
              · rcases m.htr 3 5 6 (by decide) (by decide) with h50 | h50
                · rcases m.htr 4 5 6 (by decide) (by decide) with h51 | h51
                  · linarith only [h41, h49, h51, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi5]
                  · linarith only [h21, h39, h41, h49, h51, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                · linarith only [h1, h21, h39, h41, h49, h50, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi1]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h55 | h55
                · rcases m.htr 4 5 6 (by decide) (by decide) with h56 | h56
                  · rcases h6emax with h57 | h57 | h57 | h57 | h57 | h57
                    · linarith only [h0, h57, hlam, ht56, u5ehi5]
                    · linarith only [h39, h57, hlam, ht56, u5ehi5]
                    · linarith only [h40, h57, hlam, ht56, u5ehi5]
                    · linarith only [h21, h39, h57, hlam, ht56, u5ehi5]
                    · linarith only [h21, h39, h49, h57, hlam, ht56, u5ehi5]
                    · linarith only [h57, hlam, ht56, u5ehi5]
                  · linarith only [h39, h56, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                · linarith only [h1, h39, h55, hlam]
          · linarith only [h39, h40, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
        · linarith only [h0, h39, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi1]
  · linarith only [h0, hc56, hlam, hphi, u5ehi0]

theorem n8l_sAB8_M_IR_H_I (m : N8Model)
    (hb5 : CMSig2_8_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.2.1
  have h6emax := hb6.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  rcases h6emax with h0 | h0 | h0 | h0 | h0 | h0
  · rcases m.htr 0 5 6 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, ht56, u5ehi5]
    · linarith only [h0, h1, hlam, ht56, u5ehi0]
  · rcases m.htr 0 5 6 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
      · rcases m.htr 1 3 6 (by decide) (by decide) with h6 | h6
        · rcases m.htr 1 5 6 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h7, hlam, ht56, u5ehi5]
          · linarith only [h0, h5, h7, hlam, ht56, u5ehi3]
        · linarith only [h0, h5, h6, hlam, ht56, u5ehi3]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 5 6 (by decide) (by decide) with h12 | h12
          · linarith only [h0, h12, hlam, ht56, u5ehi5]
          · linarith only [h0, h12, hlam, ht56, u5ehi1]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h15, hlam, ht56, u5ehi5]
          · linarith only [h0, h15, hlam, ht56, u5ehi1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
      · rcases m.htr 1 3 6 (by decide) (by decide) with h19 | h19
        · rcases m.htr 1 5 6 (by decide) (by decide) with h20 | h20
          · linarith only [h0, h20, h4, hlam, ht56, u5ehi0]
          · linarith only [h0, h18, h20, hlam, ht56, u5ehi3]
        · linarith only [h0, h18, h19, hlam, ht56, u5ehi3]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 5 6 (by decide) (by decide) with h25 | h25
          · linarith only [h0, h25, hlam, ht56, u5ehi5]
          · linarith only [h0, h25, hlam, ht56, u5ehi1]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h28 | h28
          · linarith only [h0, h28, h4, hlam, ht56, u5ehi0]
          · linarith only [h0, h28, hlam, ht56, u5ehi1]
  · rcases m.htr 0 5 6 (by decide) (by decide) with h31 | h31
    · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
      · rcases m.htr 1 3 6 (by decide) (by decide) with h33 | h33
        · rcases m.htr 1 5 6 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 5 6 (by decide) (by decide) with h35 | h35
            · linarith only [h0, h35, hlam, ht56, u5ehi5]
            · linarith only [h0, h35, hlam, ht56, u5ehi2]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h38 | h38
            · linarith only [h0, h38, hlam, ht56, u5ehi5]
            · linarith only [h0, h38, hlam, ht56, u5ehi2]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h41 | h41
          · linarith only [h32, h33, h41, hlam]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h43 | h43
            · linarith only [h0, h43, hlam, ht56, u5ehi5]
            · linarith only [h0, h43, hlam, ht56, u5ehi2]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h46 | h46
        · rcases m.htr 1 5 6 (by decide) (by decide) with h47 | h47
          · rcases m.htr 2 5 6 (by decide) (by decide) with h48 | h48
            · linarith only [h0, h48, hlam, ht56, u5ehi5]
            · linarith only [h0, h48, hlam, ht56, u5ehi2]
          · linarith only [h32, h46, h47, hlam]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h52 | h52
          · rcases m.htr 2 5 6 (by decide) (by decide) with h53 | h53
            · linarith only [h0, h53, hlam, ht56, u5ehi5]
            · linarith only [h0, h53, hlam, ht56, u5ehi2]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h56 | h56
            · linarith only [h0, h52, h56, hlam, ht56, u5ehi1]
            · linarith only [h0, h56, hlam, ht56, u5ehi2]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
      · rcases m.htr 1 3 6 (by decide) (by decide) with h60 | h60
        · rcases m.htr 1 5 6 (by decide) (by decide) with h61 | h61
          · rcases m.htr 2 5 6 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h31, h62, hlam, ht56, u5ehi0]
            · linarith only [h0, h62, hlam, ht56, u5ehi2]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h65 | h65
            · linarith only [h0, h61, h65, hlam, ht56, u5ehi1]
            · linarith only [h0, h65, hlam, ht56, u5ehi2]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h68 | h68
          · linarith only [h31, h59, h60, h68, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h70 | h70
            · linarith only [h0, h70, hlam, ht56, u5ehi5]
            · linarith only [h0, h70, hlam, ht56, u5ehi2]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h73 | h73
        · rcases m.htr 1 5 6 (by decide) (by decide) with h74 | h74
          · rcases m.htr 2 5 6 (by decide) (by decide) with h75 | h75
            · linarith only [h0, h75, hlam, ht56, u5ehi5]
            · linarith only [h0, h75, hlam, ht56, u5ehi2]
          · linarith only [h59, h73, h74, hlam]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h79 | h79
          · rcases m.htr 2 5 6 (by decide) (by decide) with h80 | h80
            · linarith only [h0, h31, h80, hlam, ht56, u5ehi0]
            · linarith only [h0, h80, hlam, ht56, u5ehi2]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h83 | h83
            · linarith only [h0, h31, h83, hlam, ht56, u5ehi0]
            · linarith only [h0, h83, hlam, ht56, u5ehi2]
  · rcases m.htr 0 5 6 (by decide) (by decide) with h86 | h86
    · rcases m.htr 1 3 5 (by decide) (by decide) with h87 | h87
      · rcases m.htr 1 3 6 (by decide) (by decide) with h88 | h88
        · rcases m.htr 1 5 6 (by decide) (by decide) with h89 | h89
          · rcases m.htr 2 5 6 (by decide) (by decide) with h90 | h90
            · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 3 5 6 (by decide) (by decide) with h92 | h92
                · linarith only [h0, h92, hlam, ht56, u5ehi5]
                · linarith only [h0, h91, h92, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h95 | h95
                · linarith only [h0, h95, hlam, ht56, u5ehi5]
                · linarith only [h0, h95, hlam, ht56, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
              · rcases m.htr 3 5 6 (by decide) (by decide) with h99 | h99
                · linarith only [h87, h90, h99, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · linarith only [h0, h98, h99, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h102 | h102
                · linarith only [h102, h87, h90, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · linarith only [h0, h102, hlam, ht56, u5ehi3]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h105 | h105
            · rcases m.htr 3 4 5 (by decide) (by decide) with h106 | h106
              · rcases m.htr 3 5 6 (by decide) (by decide) with h107 | h107
                · linarith only [h107, h87, h89, hlam]
                · linarith only [h0, h106, h107, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h110 | h110
                · linarith only [h110, h87, h89, hlam]
                · linarith only [h0, h110, hlam, ht56, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 3 5 6 (by decide) (by decide) with h114 | h114
                · linarith only [h114, h87, h89, hlam]
                · linarith only [h0, h113, h114, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h117 | h117
                · linarith only [h117, h87, h89, hlam]
                · linarith only [h0, h117, hlam, ht56, u5ehi3]
        · linarith only [h0, h88, hc13, hlam, ht34, ht45, ht56]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h121 | h121
        · rcases m.htr 1 5 6 (by decide) (by decide) with h122 | h122
          · rcases m.htr 2 5 6 (by decide) (by decide) with h123 | h123
            · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
              · rcases m.htr 3 5 6 (by decide) (by decide) with h125 | h125
                · linarith only [h0, h125, hlam, ht56, u5ehi5]
                · linarith only [h121, h122, h125, h87, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h128 | h128
                · linarith only [h0, h128, hlam, ht56, u5ehi5]
                · linarith only [h121, h128, h86, h87, hc05, hc36, hlam, hphi, ht0b, ht6b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
              · rcases m.htr 3 5 6 (by decide) (by decide) with h132 | h132
                · linarith only [h0, h123, h132, hlam, ht56, u5ehi2]
                · linarith only [h121, h122, h132, h87, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h135 | h135
                · linarith only [h0, h123, h135, hlam, ht56, u5ehi2]
                · linarith only [h121, h122, h135, h87, hlam]
          · linarith only [h121, h122, h87, hlam]
        · linarith only [h0, h121, hc13, hlam, ht34, ht45, ht56]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
      · rcases m.htr 1 3 6 (by decide) (by decide) with h141 | h141
        · rcases m.htr 1 5 6 (by decide) (by decide) with h142 | h142
          · rcases m.htr 2 5 6 (by decide) (by decide) with h143 | h143
            · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
              · rcases m.htr 3 5 6 (by decide) (by decide) with h145 | h145
                · linarith only [h140, h145, h86, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi0]
                · linarith only [h0, h144, h145, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h148 | h148
                · linarith only [h140, h148, h86, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi0]
                · linarith only [h0, h148, hlam, ht56, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
              · rcases m.htr 3 5 6 (by decide) (by decide) with h152 | h152
                · linarith only [h140, h152, h86, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi0]
                · linarith only [h0, h151, h152, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h155 | h155
                · linarith only [h140, h143, h155, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · linarith only [h0, h155, hlam, ht56, u5ehi3]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h158 | h158
            · rcases m.htr 3 4 5 (by decide) (by decide) with h159 | h159
              · rcases m.htr 3 5 6 (by decide) (by decide) with h160 | h160
                · linarith only [h140, h142, h160, hlam]
                · linarith only [h0, h159, h160, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h163 | h163
                · linarith only [h140, h142, h163, hlam]
                · linarith only [h0, h163, hlam, ht56, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
              · rcases m.htr 3 5 6 (by decide) (by decide) with h167 | h167
                · linarith only [h140, h142, h167, hlam]
                · linarith only [h0, h166, h167, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h170 | h170
                · linarith only [h140, h142, h170, hlam]
                · linarith only [h0, h170, hlam, ht56, u5ehi3]
        · linarith only [h0, h141, hc13, hlam, ht34, ht45, ht56]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h174 | h174
        · rcases m.htr 1 5 6 (by decide) (by decide) with h175 | h175
          · rcases m.htr 2 5 6 (by decide) (by decide) with h176 | h176
            · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
              · rcases m.htr 3 5 6 (by decide) (by decide) with h178 | h178
                · linarith only [h0, h178, hlam, ht56, u5ehi5]
                · linarith only [h140, h174, h175, h178, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h181 | h181
                · linarith only [h0, h181, h86, hlam, ht56, u5ehi0]
                · linarith only [h140, h174, h175, h181, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h184 | h184
              · rcases m.htr 3 5 6 (by decide) (by decide) with h185 | h185
                · linarith only [h0, h185, h86, hlam, ht56, u5ehi0]
                · linarith only [h140, h174, h175, h185, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h188 | h188
                · linarith only [h0, h188, h86, hlam, ht56, u5ehi0]
                · linarith only [h140, h174, h175, h188, hlam]
          · linarith only [h140, h174, h175, hlam]
        · linarith only [h0, h174, hc13, hlam, ht34, ht45, ht56]
  · rcases m.htr 0 5 6 (by decide) (by decide) with h193 | h193
    · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
      · rcases m.htr 1 3 6 (by decide) (by decide) with h195 | h195
        · rcases m.htr 1 5 6 (by decide) (by decide) with h196 | h196
          · rcases m.htr 2 5 6 (by decide) (by decide) with h197 | h197
            · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
              · rcases m.htr 3 5 6 (by decide) (by decide) with h199 | h199
                · rcases m.htr 4 5 6 (by decide) (by decide) with h200 | h200
                  · linarith only [h0, h200, hlam, ht56, u5ehi5]
                  · linarith only [h194, h199, h200, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi4]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h203 | h203
                  · linarith only [h198, h199, h203, hlam]
                  · linarith only [h0, h203, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h206 | h206
                · rcases m.htr 4 5 6 (by decide) (by decide) with h207 | h207
                  · linarith only [h0, h207, hlam, ht56, u5ehi5]
                  · linarith only [h198, h206, h207, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h210 | h210
                  · linarith only [h0, h210, hlam, ht56, u5ehi5]
                  · linarith only [h0, h198, h210, hc34, hlam, ht45, ht56]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h213 | h213
              · rcases m.htr 3 5 6 (by decide) (by decide) with h214 | h214
                · linarith only [h194, h197, h214, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h216 | h216
                  · linarith only [h213, h214, h216, hlam]
                  · linarith only [h0, h216, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h219 | h219
                · linarith only [h194, h197, h219, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h221 | h221
                  · linarith only [h0, h197, h221, hlam, ht56, u5ehi2]
                  · linarith only [h0, h213, h221, hc34, hlam, ht45, ht56]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h224 | h224
            · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
              · rcases m.htr 3 5 6 (by decide) (by decide) with h226 | h226
                · linarith only [h194, h196, h226, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h228 | h228
                  · linarith only [h194, h196, h225, h228, hlam]
                  · linarith only [h0, h228, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h231 | h231
                · linarith only [h194, h196, h231, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h233 | h233
                  · linarith only [h0, h196, h233, hlam, ht56, u5ehi1]
                  · linarith only [h0, h233, hlam, ht56, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
              · rcases m.htr 3 5 6 (by decide) (by decide) with h237 | h237
                · linarith only [h194, h224, h237, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h239 | h239
                  · linarith only [h194, h196, h236, h239, hlam]
                  · linarith only [h0, h239, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h242 | h242
                · linarith only [h194, h196, h242, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h244 | h244
                  · linarith only [h0, h196, h244, hlam, ht56, u5ehi1]
                  · linarith only [h0, h236, h244, hc34, hlam, ht45, ht56]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h247 | h247
          · linarith only [h194, h195, h247, hlam]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h249 | h249
            · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
              · rcases m.htr 3 5 6 (by decide) (by decide) with h251 | h251
                · linarith only [h194, h195, h247, h251, hlam]
                · linarith only [h193, h194, h195, h251, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi3]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h254 | h254
                · linarith only [h194, h195, h254, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                · linarith only [h194, h195, h249, h254, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h257 | h257
              · rcases m.htr 3 5 6 (by decide) (by decide) with h258 | h258
                · linarith only [h194, h249, h258, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · linarith only [h194, h195, h257, h258, hc56, hlam, hphi, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h261 | h261
                · linarith only [h194, h195, h261, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                · linarith only [h194, h195, h261, hc56, hlam, hphi, u5ehi3]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h264 | h264
        · rcases m.htr 1 5 6 (by decide) (by decide) with h265 | h265
          · rcases m.htr 2 5 6 (by decide) (by decide) with h266 | h266
            · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
              · rcases m.htr 3 5 6 (by decide) (by decide) with h268 | h268
                · rcases m.htr 4 5 6 (by decide) (by decide) with h269 | h269
                  · linarith only [h0, h269, hlam, ht56, u5ehi5]
                  · linarith only [h194, h264, h267, h268, h269, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi4]
                · linarith only [h194, h264, h266, h268, hc25, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h273 | h273
                · rcases m.htr 4 5 6 (by decide) (by decide) with h274 | h274
                  · linarith only [h0, h274, hlam, ht56, u5ehi5]
                  · linarith only [h194, h264, h267, h273, h274, hlam]
                · linarith only [h193, h194, h264, h273, hc05, hc36, hlam, hphi, ht0b, ht6b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
              · rcases m.htr 3 5 6 (by decide) (by decide) with h279 | h279
                · linarith only [h194, h264, h266, h278, h279, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi2]
                · linarith only [h193, h194, h264, h279, hc05, hc36, hlam, hphi, ht0b, ht6b]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h282 | h282
                · linarith only [h194, h264, h266, h278, h282, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi2]
                · linarith only [h194, h264, h265, h282, hc15, hc36, hlam, hphi, ht01, ht0b, ht6b]
          · linarith only [h194, h264, h265, hlam]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h286 | h286
          · rcases m.htr 2 5 6 (by decide) (by decide) with h287 | h287
            · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
              · rcases m.htr 3 5 6 (by decide) (by decide) with h289 | h289
                · rcases m.htr 4 5 6 (by decide) (by decide) with h290 | h290
                  · linarith only [h0, h290, hlam, ht56, u5ehi5]
                  · linarith only [h0, h290, hlam, ht56, u5ehi4]
                · linarith only [h194, h286, h289, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h294 | h294
                · rcases m.htr 4 5 6 (by decide) (by decide) with h295 | h295
                  · linarith only [h0, h295, hlam, ht56, u5ehi5]
                  · linarith only [h194, h286, h288, h295, hlam]
                · linarith only [h194, h286, h294, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
              · rcases m.htr 3 5 6 (by decide) (by decide) with h300 | h300
                · rcases m.htr 4 5 6 (by decide) (by decide) with h301 | h301
                  · linarith only [h287, h299, h301, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi2]
                  · linarith only [h0, h301, hlam, ht56, u5ehi4]
                · linarith only [h194, h286, h300, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h305 | h305
                · rcases m.htr 4 5 6 (by decide) (by decide) with h306 | h306
                  · linarith only [h0, h287, h306, hlam, ht56, u5ehi2]
                  · linarith only [h194, h286, h299, h306, hlam]
                · linarith only [h194, h286, h305, hlam]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h310 | h310
            · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
              · rcases m.htr 3 5 6 (by decide) (by decide) with h312 | h312
                · rcases m.htr 4 5 6 (by decide) (by decide) with h313 | h313
                  · linarith only [h286, h311, h313, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi1]
                  · linarith only [h0, h313, hlam, ht56, u5ehi4]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h316 | h316
                  · linarith only [h194, h312, h316, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h316, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h319 | h319
                · rcases m.htr 4 5 6 (by decide) (by decide) with h320 | h320
                  · linarith only [h0, h286, h320, hlam, ht56, u5ehi1]
                  · linarith only [h311, h319, h320, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h323 | h323
                  · linarith only [h194, h319, h323, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h194, h311, h323, hc13, hlam, ht34, ht45, ht56]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
              · rcases m.htr 3 5 6 (by decide) (by decide) with h327 | h327
                · rcases m.htr 4 5 6 (by decide) (by decide) with h328 | h328
                  · linarith only [h286, h326, h328, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi1]
                  · linarith only [h0, h328, hlam, ht56, u5ehi4]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h331 | h331
                  · linarith only [h194, h327, h331, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h331, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h334 | h334
                · rcases m.htr 4 5 6 (by decide) (by decide) with h335 | h335
                  · linarith only [h0, h286, h335, hlam, ht56, u5ehi1]
                  · linarith only [h326, h334, h335, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h338 | h338
                  · linarith only [h194, h334, h338, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h194, h326, h338, hc13, hlam, ht34, ht45, ht56]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h341 | h341
      · rcases m.htr 1 3 6 (by decide) (by decide) with h342 | h342
        · rcases m.htr 1 5 6 (by decide) (by decide) with h343 | h343
          · rcases m.htr 2 5 6 (by decide) (by decide) with h344 | h344
            · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
              · rcases m.htr 3 5 6 (by decide) (by decide) with h346 | h346
                · linarith only [h193, h341, h346, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi0]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h348 | h348
                  · linarith only [h345, h346, h348, hlam]
                  · linarith only [h0, h348, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h351 | h351
                · linarith only [h193, h341, h351, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi0]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h353 | h353
                  · linarith only [h0, h193, h353, hlam, ht56, u5ehi0]
                  · linarith only [h0, h345, h353, hc34, hlam, ht45, ht56]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
              · rcases m.htr 3 5 6 (by decide) (by decide) with h357 | h357
                · linarith only [h341, h344, h357, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h359 | h359
                  · linarith only [h356, h357, h359, hlam]
                  · linarith only [h0, h359, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h362 | h362
                · linarith only [h193, h341, h362, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi0]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h364 | h364
                  · linarith only [h0, h193, h364, hlam, ht56, u5ehi0]
                  · linarith only [h0, h356, h364, hc34, hlam, ht45, ht56]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h367 | h367
            · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
              · rcases m.htr 3 5 6 (by decide) (by decide) with h369 | h369
                · linarith only [h341, h343, h369, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h371 | h371
                  · linarith only [h341, h343, h368, h371, hlam]
                  · linarith only [h0, h371, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h374 | h374
                · linarith only [h341, h343, h374, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h376 | h376
                  · linarith only [h0, h343, h376, hlam, ht56, u5ehi1]
                  · linarith only [h0, h376, hlam, ht56, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
              · rcases m.htr 3 5 6 (by decide) (by decide) with h380 | h380
                · linarith only [h341, h367, h380, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h382 | h382
                  · linarith only [h341, h343, h379, h382, hlam]
                  · linarith only [h0, h382, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h385 | h385
                · linarith only [h341, h343, h385, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h387 | h387
                  · linarith only [h0, h343, h387, hlam, ht56, u5ehi1]
                  · linarith only [h0, h379, h387, hc34, hlam, ht45, ht56]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h390 | h390
          · linarith only [h193, h341, h342, h390, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h392 | h392
            · rcases m.htr 3 4 5 (by decide) (by decide) with h393 | h393
              · rcases m.htr 3 5 6 (by decide) (by decide) with h394 | h394
                · linarith only [h341, h342, h390, h394, hlam]
                · linarith only [h341, h342, h394, hc56, hlam, hphi, u5ehi3]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h397 | h397
                · linarith only [h341, h342, h397, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                · linarith only [h341, h342, h397, hc56, hlam, hphi, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h400 | h400
              · rcases m.htr 3 5 6 (by decide) (by decide) with h401 | h401
                · linarith only [h341, h392, h401, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, u5ehi2]
                · linarith only [h341, h342, h400, h401, hc56, hlam, hphi, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h404 | h404
                · linarith only [h341, h342, h404, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi5]
                · linarith only [h341, h342, h404, hc56, hlam, hphi, u5ehi3]
      · rcases m.htr 1 3 6 (by decide) (by decide) with h407 | h407
        · rcases m.htr 1 5 6 (by decide) (by decide) with h408 | h408
          · rcases m.htr 2 5 6 (by decide) (by decide) with h409 | h409
            · rcases m.htr 3 4 5 (by decide) (by decide) with h410 | h410
              · rcases m.htr 3 5 6 (by decide) (by decide) with h411 | h411
                · linarith only [h193, h341, h407, h410, h411, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
                · linarith only [h341, h407, h408, h411, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h414 | h414
                · linarith only [h193, h341, h407, h414, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
                · linarith only [h341, h407, h408, h414, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h417 | h417
              · rcases m.htr 3 5 6 (by decide) (by decide) with h418 | h418
                · linarith only [h193, h341, h407, h417, h418, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
                · linarith only [h341, h408, h418, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h421 | h421
                · linarith only [h341, h407, h409, h417, h421, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b, u5ehi2]
                · linarith only [h341, h407, h408, h421, hc15, hc36, hlam, hphi, ht01, ht0b, ht6b]
          · linarith only [h341, h407, h408, hlam]
        · rcases m.htr 1 5 6 (by decide) (by decide) with h425 | h425
          · rcases m.htr 2 5 6 (by decide) (by decide) with h426 | h426
            · rcases m.htr 3 4 5 (by decide) (by decide) with h427 | h427
              · rcases m.htr 3 5 6 (by decide) (by decide) with h428 | h428
                · rcases m.htr 4 5 6 (by decide) (by decide) with h429 | h429
                  · linarith only [h193, h427, h429, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
                  · linarith only [h0, h429, hlam, ht56, u5ehi4]
                · linarith only [h341, h425, h428, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h433 | h433
                · rcases m.htr 4 5 6 (by decide) (by decide) with h434 | h434
                  · linarith only [h0, h434, hlam, ht56, u5ehi5]
                  · linarith only [h341, h425, h427, h434, hlam]
                · linarith only [h341, h425, h433, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h438 | h438
              · rcases m.htr 3 5 6 (by decide) (by decide) with h439 | h439
                · rcases m.htr 4 5 6 (by decide) (by decide) with h440 | h440
                  · linarith only [h193, h438, h440, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi0]
                  · linarith only [h0, h440, hlam, ht56, u5ehi4]
                · linarith only [h341, h425, h439, hlam]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h444 | h444
                · rcases m.htr 4 5 6 (by decide) (by decide) with h445 | h445
                  · linarith only [h0, h193, h445, hlam, ht56, u5ehi0]
                  · linarith only [h341, h425, h438, h445, hlam]
                · linarith only [h341, h425, h444, hlam]
          · rcases m.htr 2 5 6 (by decide) (by decide) with h449 | h449
            · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
              · rcases m.htr 3 5 6 (by decide) (by decide) with h451 | h451
                · rcases m.htr 4 5 6 (by decide) (by decide) with h452 | h452
                  · linarith only [h425, h450, h452, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi1]
                  · linarith only [h0, h452, hlam, ht56, u5ehi4]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h455 | h455
                  · linarith only [h341, h451, h455, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h455, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h458 | h458
                · rcases m.htr 4 5 6 (by decide) (by decide) with h459 | h459
                  · linarith only [h0, h193, h459, hlam, ht56, u5ehi0]
                  · linarith only [h450, h458, h459, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h462 | h462
                  · linarith only [h341, h458, h462, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h341, h450, h462, hc13, hlam, ht34, ht45, ht56]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h465 | h465
              · rcases m.htr 3 5 6 (by decide) (by decide) with h466 | h466
                · rcases m.htr 4 5 6 (by decide) (by decide) with h467 | h467
                  · linarith only [h425, h465, h467, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b, u5ehi1]
                  · linarith only [h0, h467, hlam, ht56, u5ehi4]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h470 | h470
                  · linarith only [h341, h466, h470, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h470, hlam, ht56, u5ehi4]
              · rcases m.htr 3 5 6 (by decide) (by decide) with h473 | h473
                · rcases m.htr 4 5 6 (by decide) (by decide) with h474 | h474
                  · linarith only [h0, h449, h474, hlam, ht56, u5ehi2]
                  · linarith only [h465, h473, h474, hlam]
                · rcases m.htr 4 5 6 (by decide) (by decide) with h477 | h477
                  · linarith only [h341, h473, h477, hc13, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h341, h465, h477, hc13, hlam, ht34, ht45, ht56]
  · linarith only [h0, hlam, ht56, u5ehi5]

theorem n8l_sAB8_M_IR_H_R (m : N8Model)
    (hb5 : CMSig2_8_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h6ehi := hb6.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 5) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 5) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 5 6) (by simp) with h8 | h8
              · linarith only [h8, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h8, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h11 | h11
              · linarith only [h11, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h11, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · rcases p0_3 (m.d 5 6) (by simp) with h15 | h15
              · linarith only [h15, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h15, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h18 | h18
              · linarith only [h18, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h18, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h21 | h21
          · rcases p0_3 (m.d 4 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 5 6) (by simp) with h23 | h23
              · linarith only [h23, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h23, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h26 | h26
              · linarith only [h26, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h26, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · rcases p0_3 (m.d 5 6) (by simp) with h30 | h30
              · linarith only [h30, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h30, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h33 | h33
              · linarith only [h33, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h33, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
    · rcases p0_3 (m.d 1 5) (by simp) with h38 | h38
      · rcases p0_3 (m.d 2 5) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h41 | h41
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases p0_3 (m.d 5 6) (by simp) with h43 | h43
              · linarith only [h43, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h43, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h46 | h46
              · linarith only [h46, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h46, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · rcases p0_3 (m.d 5 6) (by simp) with h50 | h50
              · linarith only [h50, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h50, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h53 | h53
              · linarith only [h53, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h53, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h58 | h58
          · rcases p0_3 (m.d 4 5) (by simp) with h59 | h59
            · rcases p0_3 (m.d 5 6) (by simp) with h60 | h60
              · linarith only [h38, h60, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h60, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h63 | h63
              · linarith only [h38, h63, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h63, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · rcases p0_3 (m.d 5 6) (by simp) with h67 | h67
              · linarith only [h38, h67, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h67, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h70 | h70
              · linarith only [h70, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h70, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h37, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
    · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
      · rcases p0_3 (m.d 2 5) (by simp) with h76 | h76
        · rcases p0_3 (m.d 3 5) (by simp) with h77 | h77
          · linarith only [h77, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h79 | h79
            · rcases p0_3 (m.d 5 6) (by simp) with h80 | h80
              · linarith only [h80, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h80, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h83 | h83
              · linarith only [h83, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h83, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · rcases p0_3 (m.d 5 6) (by simp) with h89 | h89
              · linarith only [h76, h89, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h89, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h92 | h92
              · linarith only [h76, h92, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h92, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 5) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · rcases p0_3 (m.d 5 6) (by simp) with h99 | h99
              · linarith only [h75, h99, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h99, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h102 | h102
              · linarith only [h102, h75, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h102, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · rcases p0_3 (m.d 5 6) (by simp) with h108 | h108
              · linarith only [h108, h75, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h108, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h111 | h111
              · linarith only [h111, h75, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h111, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h74, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h115 | h115
    · rcases p0_3 (m.d 1 5) (by simp) with h116 | h116
      · rcases p0_3 (m.d 2 5) (by simp) with h117 | h117
        · rcases p0_3 (m.d 3 5) (by simp) with h118 | h118
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h121 | h121
              · linarith only [h121, hc56, hlam, hphi, p0_1, u5ehi4]
              · linarith only [h121, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h126 | h126
              · linarith only [h118, h126, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h126, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h129 | h129
          · rcases p0_3 (m.d 4 5) (by simp) with h130 | h130
            · linarith only [h130, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h132 | h132
              · linarith only [h117, h132, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h132, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h137 | h137
              · linarith only [h117, h137, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h137, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
      · rcases p0_3 (m.d 2 5) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 5) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h144 | h144
              · linarith only [h116, h144, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h144, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h149 | h149
              · linarith only [h116, h149, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h149, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h155 | h155
              · linarith only [h116, h155, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h155, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h158 | h158
            · linarith only [h158, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h160 | h160
              · linarith only [h116, h160, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h160, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
    · linarith only [h115, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
    · linarith only [h165, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h167 | h167
      · rcases p0_3 (m.d 2 5) (by simp) with h168 | h168
        · rcases p0_3 (m.d 3 5) (by simp) with h169 | h169
          · rcases p0_3 (m.d 4 5) (by simp) with h170 | h170
            · rcases p0_3 (m.d 5 6) (by simp) with h171 | h171
              · linarith only [h171, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h171, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h174 | h174
              · linarith only [h174, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h174, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h177 | h177
            · rcases p0_3 (m.d 5 6) (by simp) with h178 | h178
              · linarith only [h178, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h178, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h181 | h181
              · linarith only [h181, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h181, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h184 | h184
          · rcases p0_3 (m.d 4 5) (by simp) with h185 | h185
            · rcases p0_3 (m.d 5 6) (by simp) with h186 | h186
              · linarith only [h186, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h186, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h189 | h189
              · linarith only [h189, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h189, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h192 | h192
            · rcases p0_3 (m.d 5 6) (by simp) with h193 | h193
              · linarith only [h193, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h193, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h196 | h196
              · linarith only [h196, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h196, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h167, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h201 | h201
    · rcases p0_3 (m.d 1 5) (by simp) with h202 | h202
      · rcases p0_3 (m.d 2 5) (by simp) with h203 | h203
        · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h205 | h205
          · rcases p0_3 (m.d 4 5) (by simp) with h206 | h206
            · rcases p0_3 (m.d 5 6) (by simp) with h207 | h207
              · linarith only [h207, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h201, h207, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h210 | h210
              · linarith only [h210, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h210, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases p0_3 (m.d 5 6) (by simp) with h214 | h214
              · linarith only [h214, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h214, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h217 | h217
              · linarith only [h217, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h217, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h202, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h221 | h221
      · rcases p0_3 (m.d 2 5) (by simp) with h222 | h222
        · linarith only [h222, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h224 | h224
          · rcases p0_3 (m.d 4 5) (by simp) with h225 | h225
            · rcases p0_3 (m.d 5 6) (by simp) with h226 | h226
              · linarith only [h201, h226, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h226, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h229 | h229
              · linarith only [h201, h229, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h229, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · rcases p0_3 (m.d 5 6) (by simp) with h233 | h233
              · linarith only [h201, h233, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h233, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h236 | h236
              · linarith only [h201, h236, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h236, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h221, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h240 | h240
    · rcases p0_3 (m.d 1 5) (by simp) with h241 | h241
      · rcases p0_3 (m.d 2 5) (by simp) with h242 | h242
        · rcases p0_3 (m.d 3 5) (by simp) with h243 | h243
          · linarith only [h243, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h245 | h245
            · rcases p0_3 (m.d 5 6) (by simp) with h246 | h246
              · linarith only [h246, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h240, h246, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h249 | h249
              · linarith only [h249, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h240, h249, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h254 | h254
            · rcases p0_3 (m.d 5 6) (by simp) with h255 | h255
              · linarith only [h242, h255, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h255, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h258 | h258
              · linarith only [h242, h258, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h258, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h241, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h262 | h262
      · rcases p0_3 (m.d 2 5) (by simp) with h263 | h263
        · rcases p0_3 (m.d 3 5) (by simp) with h264 | h264
          · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h266 | h266
            · rcases p0_3 (m.d 5 6) (by simp) with h267 | h267
              · linarith only [h240, h267, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h267, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h270 | h270
              · linarith only [h240, h270, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h270, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h275 | h275
            · rcases p0_3 (m.d 5 6) (by simp) with h276 | h276
              · linarith only [h240, h276, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h276, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h279 | h279
              · linarith only [h240, h279, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h279, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h262, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h283 | h283
    · rcases p0_3 (m.d 1 5) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 5) (by simp) with h285 | h285
        · rcases p0_3 (m.d 3 5) (by simp) with h286 | h286
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h289 | h289
              · linarith only [h289, hc56, hlam, hphi, p0_1, u5ehi4]
              · linarith only [h283, h289, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h292 | h292
            · linarith only [h292, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h294 | h294
              · linarith only [h286, h294, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h294, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h297 | h297
          · rcases p0_3 (m.d 4 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h300 | h300
              · linarith only [h285, h300, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h300, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h303 | h303
            · linarith only [h303, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h305 | h305
              · linarith only [h285, h305, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h305, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h284, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h309 | h309
      · rcases p0_3 (m.d 2 5) (by simp) with h310 | h310
        · rcases p0_3 (m.d 3 5) (by simp) with h311 | h311
          · rcases p0_3 (m.d 4 5) (by simp) with h312 | h312
            · linarith only [h312, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h314 | h314
              · linarith only [h283, h314, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h314, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h319 | h319
              · linarith only [h283, h319, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h319, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
        · rcases p0_3 (m.d 3 5) (by simp) with h322 | h322
          · rcases p0_3 (m.d 4 5) (by simp) with h323 | h323
            · linarith only [h323, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h325 | h325
              · linarith only [h283, h325, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h325, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h328 | h328
            · linarith only [h328, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h330 | h330
              · linarith only [h283, h330, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h330, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
      · linarith only [h309, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h335 | h335
    · linarith only [h335, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h337 | h337
      · rcases p0_3 (m.d 2 5) (by simp) with h338 | h338
        · rcases p0_3 (m.d 3 5) (by simp) with h339 | h339
          · rcases p0_3 (m.d 4 5) (by simp) with h340 | h340
            · rcases p0_3 (m.d 5 6) (by simp) with h341 | h341
              · linarith only [h341, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h341, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h344 | h344
              · linarith only [h344, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h344, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h347 | h347
            · rcases p0_3 (m.d 5 6) (by simp) with h348 | h348
              · linarith only [h348, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h348, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h351 | h351
              · linarith only [h351, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h351, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h338, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h355 | h355
        · rcases p0_3 (m.d 3 5) (by simp) with h356 | h356
          · rcases p0_3 (m.d 4 5) (by simp) with h357 | h357
            · rcases p0_3 (m.d 5 6) (by simp) with h358 | h358
              · linarith only [h358, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h358, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h361 | h361
              · linarith only [h361, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h361, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h364 | h364
            · rcases p0_3 (m.d 5 6) (by simp) with h365 | h365
              · linarith only [h365, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h365, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h368 | h368
              · linarith only [h368, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h368, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h355, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h372 | h372
    · rcases p0_3 (m.d 1 5) (by simp) with h373 | h373
      · linarith only [h373, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h375 | h375
        · rcases p0_3 (m.d 3 5) (by simp) with h376 | h376
          · rcases p0_3 (m.d 4 5) (by simp) with h377 | h377
            · rcases p0_3 (m.d 5 6) (by simp) with h378 | h378
              · linarith only [h378, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h372, h378, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h381 | h381
              · linarith only [h381, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h381, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h384 | h384
            · rcases p0_3 (m.d 5 6) (by simp) with h385 | h385
              · linarith only [h385, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h385, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h388 | h388
              · linarith only [h388, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h388, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h375, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h392 | h392
      · linarith only [h392, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h394 | h394
        · rcases p0_3 (m.d 3 5) (by simp) with h395 | h395
          · rcases p0_3 (m.d 4 5) (by simp) with h396 | h396
            · rcases p0_3 (m.d 5 6) (by simp) with h397 | h397
              · linarith only [h372, h397, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h397, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h400 | h400
              · linarith only [h372, h400, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h400, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h403 | h403
            · rcases p0_3 (m.d 5 6) (by simp) with h404 | h404
              · linarith only [h372, h404, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h404, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h407 | h407
              · linarith only [h372, h407, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h407, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h394, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h412 | h412
    · rcases p0_3 (m.d 1 5) (by simp) with h413 | h413
      · rcases p0_3 (m.d 2 5) (by simp) with h414 | h414
        · rcases p0_3 (m.d 3 5) (by simp) with h415 | h415
          · linarith only [h415, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h417 | h417
            · rcases p0_3 (m.d 5 6) (by simp) with h418 | h418
              · linarith only [h418, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h412, h418, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h421 | h421
              · linarith only [h421, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h412, h421, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
        · linarith only [h414, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h425 | h425
        · rcases p0_3 (m.d 3 5) (by simp) with h426 | h426
          · linarith only [h426, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h428 | h428
            · rcases p0_3 (m.d 5 6) (by simp) with h429 | h429
              · linarith only [h413, h429, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h429, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h432 | h432
              · linarith only [h413, h432, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h432, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h425, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h436 | h436
      · rcases p0_3 (m.d 2 5) (by simp) with h437 | h437
        · rcases p0_3 (m.d 3 5) (by simp) with h438 | h438
          · linarith only [h438, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h440 | h440
            · rcases p0_3 (m.d 5 6) (by simp) with h441 | h441
              · linarith only [h412, h441, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h436, h441, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h444 | h444
              · linarith only [h412, h444, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h444, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h437, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h448 | h448
        · rcases p0_3 (m.d 3 5) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h451 | h451
            · rcases p0_3 (m.d 5 6) (by simp) with h452 | h452
              · linarith only [h412, h452, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h452, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h455 | h455
              · linarith only [h412, h455, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h455, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h448, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h459 | h459
    · rcases p0_3 (m.d 1 5) (by simp) with h460 | h460
      · rcases p0_3 (m.d 2 5) (by simp) with h461 | h461
        · rcases p0_3 (m.d 3 5) (by simp) with h462 | h462
          · rcases p0_3 (m.d 4 5) (by simp) with h463 | h463
            · linarith only [h463, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h465 | h465
              · linarith only [h465, hc56, hlam, hphi, p0_1, u5ehi4]
              · linarith only [h459, h465, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · linarith only [h468, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h470 | h470
              · linarith only [h462, h470, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h470, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h474 | h474
        · rcases p0_3 (m.d 3 5) (by simp) with h475 | h475
          · rcases p0_3 (m.d 4 5) (by simp) with h476 | h476
            · linarith only [h476, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h478 | h478
              · linarith only [h460, h478, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h481 | h481
            · linarith only [h481, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h483 | h483
              · linarith only [h460, h483, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h483, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h474, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h487 | h487
      · rcases p0_3 (m.d 2 5) (by simp) with h488 | h488
        · rcases p0_3 (m.d 3 5) (by simp) with h489 | h489
          · rcases p0_3 (m.d 4 5) (by simp) with h490 | h490
            · linarith only [h490, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h492 | h492
              · linarith only [h459, h492, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h487, h492, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h495 | h495
            · linarith only [h495, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h497 | h497
              · linarith only [h459, h497, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h497, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h501 | h501
        · rcases p0_3 (m.d 3 5) (by simp) with h502 | h502
          · rcases p0_3 (m.d 4 5) (by simp) with h503 | h503
            · linarith only [h503, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h505 | h505
              · linarith only [h459, h505, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · rcases p0_3 (m.d 4 5) (by simp) with h508 | h508
            · linarith only [h508, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h510 | h510
              · linarith only [h459, h510, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h510, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
        · linarith only [h501, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h515 | h515
    · linarith only [h515, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h517 | h517
      · rcases p0_3 (m.d 2 5) (by simp) with h518 | h518
        · rcases p0_3 (m.d 3 5) (by simp) with h519 | h519
          · rcases p0_3 (m.d 4 5) (by simp) with h520 | h520
            · rcases p0_3 (m.d 5 6) (by simp) with h521 | h521
              · linarith only [h521, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h517, h521, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h524 | h524
              · linarith only [h524, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h524, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h519, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h528 | h528
          · rcases p0_3 (m.d 4 5) (by simp) with h529 | h529
            · rcases p0_3 (m.d 5 6) (by simp) with h530 | h530
              · linarith only [h530, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h530, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h533 | h533
              · linarith only [h533, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h533, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h528, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h537 | h537
        · rcases p0_3 (m.d 3 5) (by simp) with h538 | h538
          · rcases p0_3 (m.d 4 5) (by simp) with h539 | h539
            · rcases p0_3 (m.d 5 6) (by simp) with h540 | h540
              · linarith only [h540, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h537, h540, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h543 | h543
              · linarith only [h543, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h543, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h538, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h547 | h547
          · rcases p0_3 (m.d 4 5) (by simp) with h548 | h548
            · rcases p0_3 (m.d 5 6) (by simp) with h549 | h549
              · linarith only [h549, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h549, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h552 | h552
              · linarith only [h552, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h552, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h547, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h556 | h556
    · rcases p0_3 (m.d 1 5) (by simp) with h557 | h557
      · linarith only [h557, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h559 | h559
        · rcases p0_3 (m.d 3 5) (by simp) with h560 | h560
          · rcases p0_3 (m.d 4 5) (by simp) with h561 | h561
            · rcases p0_3 (m.d 5 6) (by simp) with h562 | h562
              · linarith only [h562, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h556, h562, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h565 | h565
              · linarith only [h565, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h565, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h560, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h569 | h569
          · rcases p0_3 (m.d 4 5) (by simp) with h570 | h570
            · rcases p0_3 (m.d 5 6) (by simp) with h571 | h571
              · linarith only [h571, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h571, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h574 | h574
              · linarith only [h574, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h574, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h569, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h578 | h578
      · linarith only [h578, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h580 | h580
        · rcases p0_3 (m.d 3 5) (by simp) with h581 | h581
          · rcases p0_3 (m.d 4 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 5 6) (by simp) with h583 | h583
              · linarith only [h556, h583, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h580, h583, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h586 | h586
              · linarith only [h556, h586, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h586, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h581, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h590 | h590
          · rcases p0_3 (m.d 4 5) (by simp) with h591 | h591
            · rcases p0_3 (m.d 5 6) (by simp) with h592 | h592
              · linarith only [h556, h592, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h592, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h595 | h595
              · linarith only [h556, h595, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h595, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h590, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h599 | h599
    · rcases p0_3 (m.d 1 5) (by simp) with h600 | h600
      · rcases p0_3 (m.d 2 5) (by simp) with h601 | h601
        · linarith only [h601, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h603 | h603
          · rcases p0_3 (m.d 4 5) (by simp) with h604 | h604
            · rcases p0_3 (m.d 5 6) (by simp) with h605 | h605
              · linarith only [h605, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h599, h605, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h608 | h608
              · linarith only [h608, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h599, h608, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h603, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h612 | h612
        · linarith only [h612, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h614 | h614
          · rcases p0_3 (m.d 4 5) (by simp) with h615 | h615
            · rcases p0_3 (m.d 5 6) (by simp) with h616 | h616
              · linarith only [h600, h616, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h616, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h619 | h619
              · linarith only [h600, h619, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h619, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h614, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h623 | h623
      · rcases p0_3 (m.d 2 5) (by simp) with h624 | h624
        · linarith only [h624, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h626 | h626
          · rcases p0_3 (m.d 4 5) (by simp) with h627 | h627
            · rcases p0_3 (m.d 5 6) (by simp) with h628 | h628
              · linarith only [h599, h628, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h623, h628, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h631 | h631
              · linarith only [h599, h631, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h631, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h626, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h635 | h635
        · linarith only [h635, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h637 | h637
          · rcases p0_3 (m.d 4 5) (by simp) with h638 | h638
            · rcases p0_3 (m.d 5 6) (by simp) with h639 | h639
              · linarith only [h599, h639, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h639, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · rcases p0_3 (m.d 5 6) (by simp) with h642 | h642
              · linarith only [h599, h642, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h642, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h637, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h647 | h647
    · rcases p0_3 (m.d 1 5) (by simp) with h648 | h648
      · rcases p0_3 (m.d 2 5) (by simp) with h649 | h649
        · rcases p0_3 (m.d 3 5) (by simp) with h650 | h650
          · rcases p0_3 (m.d 4 5) (by simp) with h651 | h651
            · linarith only [h651, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h653 | h653
              · linarith only [h653, hc56, hlam, hphi, p0_1, u5ehi4]
              · linarith only [h647, h653, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h650, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h657 | h657
          · rcases p0_3 (m.d 4 5) (by simp) with h658 | h658
            · linarith only [h658, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h660 | h660
              · linarith only [h649, h660, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h660, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h657, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h664 | h664
        · rcases p0_3 (m.d 3 5) (by simp) with h665 | h665
          · rcases p0_3 (m.d 4 5) (by simp) with h666 | h666
            · linarith only [h666, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h668 | h668
              · linarith only [h648, h668, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h664, h668, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · linarith only [h665, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h672 | h672
          · rcases p0_3 (m.d 4 5) (by simp) with h673 | h673
            · linarith only [h673, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h675 | h675
              · linarith only [h648, h675, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h675, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h672, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h679 | h679
      · rcases p0_3 (m.d 2 5) (by simp) with h680 | h680
        · rcases p0_3 (m.d 3 5) (by simp) with h681 | h681
          · rcases p0_3 (m.d 4 5) (by simp) with h682 | h682
            · linarith only [h682, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h684 | h684
              · linarith only [h647, h684, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h679, h684, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h681, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h688 | h688
          · rcases p0_3 (m.d 4 5) (by simp) with h689 | h689
            · linarith only [h689, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h691 | h691
              · linarith only [h647, h691, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h679, h691, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
          · linarith only [h688, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h695 | h695
        · rcases p0_3 (m.d 3 5) (by simp) with h696 | h696
          · rcases p0_3 (m.d 4 5) (by simp) with h697 | h697
            · linarith only [h697, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h699 | h699
              · linarith only [h647, h699, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h695, h699, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
          · linarith only [h696, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h703 | h703
          · rcases p0_3 (m.d 4 5) (by simp) with h704 | h704
            · linarith only [h704, hlam, p0_0]
            · rcases p0_3 (m.d 5 6) (by simp) with h706 | h706
              · linarith only [h647, h706, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h706, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
          · linarith only [h703, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h711 | h711
    · linarith only [h711, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h713 | h713
      · rcases p0_3 (m.d 2 5) (by simp) with h714 | h714
        · rcases p0_3 (m.d 3 5) (by simp) with h715 | h715
          · rcases p0_3 (m.d 4 5) (by simp) with h716 | h716
            · rcases p0_3 (m.d 5 6) (by simp) with h717 | h717
              · linarith only [h717, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h713, h717, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h716, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h721 | h721
            · rcases p0_3 (m.d 5 6) (by simp) with h722 | h722
              · linarith only [h722, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h722, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h721, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h726 | h726
          · rcases p0_3 (m.d 4 5) (by simp) with h727 | h727
            · rcases p0_3 (m.d 5 6) (by simp) with h728 | h728
              · linarith only [h728, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h726, h728, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h727, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h732 | h732
            · rcases p0_3 (m.d 5 6) (by simp) with h733 | h733
              · linarith only [h733, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h733, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h732, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h737 | h737
        · rcases p0_3 (m.d 3 5) (by simp) with h738 | h738
          · rcases p0_3 (m.d 4 5) (by simp) with h739 | h739
            · rcases p0_3 (m.d 5 6) (by simp) with h740 | h740
              · linarith only [h740, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h737, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h739, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h744 | h744
            · rcases p0_3 (m.d 5 6) (by simp) with h745 | h745
              · linarith only [h745, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h745, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h744, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h749 | h749
          · rcases p0_3 (m.d 4 5) (by simp) with h750 | h750
            · rcases p0_3 (m.d 5 6) (by simp) with h751 | h751
              · linarith only [h751, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h749, h751, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h750, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h755 | h755
            · rcases p0_3 (m.d 5 6) (by simp) with h756 | h756
              · linarith only [h756, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h756, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h755, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h760 | h760
    · rcases p0_3 (m.d 1 5) (by simp) with h761 | h761
      · linarith only [h761, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h763 | h763
        · rcases p0_3 (m.d 3 5) (by simp) with h764 | h764
          · rcases p0_3 (m.d 4 5) (by simp) with h765 | h765
            · rcases p0_3 (m.d 5 6) (by simp) with h766 | h766
              · linarith only [h766, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h760, h766, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h765, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h770 | h770
            · rcases p0_3 (m.d 5 6) (by simp) with h771 | h771
              · linarith only [h771, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h771, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h770, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h775 | h775
          · rcases p0_3 (m.d 4 5) (by simp) with h776 | h776
            · rcases p0_3 (m.d 5 6) (by simp) with h777 | h777
              · linarith only [h777, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h775, h777, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h776, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h781 | h781
            · rcases p0_3 (m.d 5 6) (by simp) with h782 | h782
              · linarith only [h782, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h782, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h781, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h786 | h786
      · linarith only [h786, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h788 | h788
        · rcases p0_3 (m.d 3 5) (by simp) with h789 | h789
          · rcases p0_3 (m.d 4 5) (by simp) with h790 | h790
            · rcases p0_3 (m.d 5 6) (by simp) with h791 | h791
              · linarith only [h760, h791, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h788, h791, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h790, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h795 | h795
            · rcases p0_3 (m.d 5 6) (by simp) with h796 | h796
              · linarith only [h796, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h788, h796, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h795, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h800 | h800
          · rcases p0_3 (m.d 4 5) (by simp) with h801 | h801
            · rcases p0_3 (m.d 5 6) (by simp) with h802 | h802
              · linarith only [h802, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h800, h802, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h801, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h806 | h806
            · rcases p0_3 (m.d 5 6) (by simp) with h807 | h807
              · linarith only [h807, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h807, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h806, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h811 | h811
    · rcases p0_3 (m.d 1 5) (by simp) with h812 | h812
      · rcases p0_3 (m.d 2 5) (by simp) with h813 | h813
        · linarith only [h813, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h815 | h815
          · rcases p0_3 (m.d 4 5) (by simp) with h816 | h816
            · rcases p0_3 (m.d 5 6) (by simp) with h817 | h817
              · linarith only [h817, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h811, h817, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h816, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h821 | h821
            · rcases p0_3 (m.d 5 6) (by simp) with h822 | h822
              · linarith only [h822, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h822, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h821, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h826 | h826
        · linarith only [h826, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h828 | h828
          · rcases p0_3 (m.d 4 5) (by simp) with h829 | h829
            · rcases p0_3 (m.d 5 6) (by simp) with h830 | h830
              · linarith only [h812, h830, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h828, h830, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h829, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h834 | h834
            · rcases p0_3 (m.d 5 6) (by simp) with h835 | h835
              · linarith only [h812, h835, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h835, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h834, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h839 | h839
      · rcases p0_3 (m.d 2 5) (by simp) with h840 | h840
        · linarith only [h840, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h842 | h842
          · rcases p0_3 (m.d 4 5) (by simp) with h843 | h843
            · rcases p0_3 (m.d 5 6) (by simp) with h844 | h844
              · linarith only [h811, h844, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h839, h844, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h843, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h848 | h848
            · rcases p0_3 (m.d 5 6) (by simp) with h849 | h849
              · linarith only [h849, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h849, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h848, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h853 | h853
        · linarith only [h853, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h855 | h855
          · rcases p0_3 (m.d 4 5) (by simp) with h856 | h856
            · rcases p0_3 (m.d 5 6) (by simp) with h857 | h857
              · linarith only [h839, h857, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h855, h857, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, p0_1, u6ehi5]
            · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h861 | h861
            · rcases p0_3 (m.d 5 6) (by simp) with h862 | h862
              · linarith only [h839, h862, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h862, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h861, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h866 | h866
    · rcases p0_3 (m.d 1 5) (by simp) with h867 | h867
      · rcases p0_3 (m.d 2 5) (by simp) with h868 | h868
        · rcases p0_3 (m.d 3 5) (by simp) with h869 | h869
          · linarith only [h869, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h871 | h871
            · rcases p0_3 (m.d 5 6) (by simp) with h872 | h872
              · linarith only [h872, hc56, hlam, hphi, p0_1, u5ehi3]
              · linarith only [h866, h872, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h871, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h876 | h876
          · linarith only [h876, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 5 6) (by simp) with h879 | h879
              · linarith only [h868, h879, hc56, hlam, hphi, p0_1, u5ehi2]
              · linarith only [h879, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h878, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h883 | h883
        · rcases p0_3 (m.d 3 5) (by simp) with h884 | h884
          · linarith only [h884, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h886 | h886
            · rcases p0_3 (m.d 5 6) (by simp) with h887 | h887
              · linarith only [h867, h887, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h883, h887, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h886, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h891 | h891
          · linarith only [h891, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h893 | h893
            · rcases p0_3 (m.d 5 6) (by simp) with h894 | h894
              · linarith only [h867, h894, hc56, hlam, hphi, p0_1, u5ehi1]
              · linarith only [h894, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h893, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h898 | h898
      · rcases p0_3 (m.d 2 5) (by simp) with h899 | h899
        · rcases p0_3 (m.d 3 5) (by simp) with h900 | h900
          · linarith only [h900, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h902 | h902
            · rcases p0_3 (m.d 5 6) (by simp) with h903 | h903
              · linarith only [h866, h903, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h898, h903, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h902, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h907 | h907
          · linarith only [h907, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h909 | h909
            · rcases p0_3 (m.d 5 6) (by simp) with h910 | h910
              · linarith only [h866, h910, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h898, h910, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1, u6ehi5]
            · linarith only [h909, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h914 | h914
        · rcases p0_3 (m.d 3 5) (by simp) with h915 | h915
          · linarith only [h915, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h917 | h917
            · rcases p0_3 (m.d 5 6) (by simp) with h918 | h918
              · linarith only [h866, h918, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h914, h918, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b, p0_1, u6ehi5]
            · linarith only [h917, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h922 | h922
          · linarith only [h922, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h924 | h924
            · rcases p0_3 (m.d 5 6) (by simp) with h925 | h925
              · linarith only [h866, h925, hc56, hlam, hphi, p0_1, u5ehi0]
              · linarith only [h925, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
            · linarith only [h924, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, p0_1, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u5ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u5ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u5ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u5ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAB8_M_LI_M_LI (m : N8Model)
    (hb5 : CMSig2_8_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h6elo := hb6.1
  have h6bigk := hb6.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
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
    rcases p0_3 (m.d 0 5) (by simp) with h6 | h6
    · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
      · rcases p0_3 (m.d 2 5) (by simp) with h8 | h8
        · rcases p0_3 (m.d 3 5) (by simp) with h9 | h9
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · rcases p0_3 (m.d 5 6) (by simp) with h11 | h11
              · linarith only [h11, hlam, p0_0]
              · rcases h6bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hlam, p13_0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc16, hlam, hphi, p13_1, u6elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc26, hlam, hphi, p13_1, u6elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc36, hlam, hphi, p13_1, u6elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc46, hlam, hphi, p13_1, u6elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc56, hlam, hphi, p13_1, u6elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc06, hlam, hphi, p13_1, u6elo1]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hlam, p13_0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc26, hlam, hphi, p13_1, u6elo1]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc36, hlam, hphi, p13_1, u6elo1]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc46, hlam, hphi, p13_1, u6elo1]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc56, hlam, hphi, p13_1, u6elo1]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc06, hlam, hphi, p13_1, u6elo2]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc16, hlam, hphi, p13_1, u6elo2]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hlam, p13_0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc36, hlam, hphi, p13_1, u6elo2]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc46, hlam, hphi, p13_1, u6elo2]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc56, hlam, hphi, p13_1, u6elo2]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc06, hlam, hphi, p13_1, u6elo3]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc16, hlam, hphi, p13_1, u6elo3]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc26, hlam, hphi, p13_1, u6elo3]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hlam, p13_0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc46, hlam, hphi, p13_1, u6elo3]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc56, hlam, hphi, p13_1, u6elo3]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc06, hlam, hphi, p13_1, u6elo4]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc16, hlam, hphi, p13_1, u6elo4]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc26, hlam, hphi, p13_1, u6elo4]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc36, hlam, hphi, p13_1, u6elo4]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hlam, p13_0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc56, hlam, hphi, p13_1, u6elo4]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc06, hlam, hphi, p13_1, u6elo5]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p13_1, u5elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p13_1, u5elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p13_1, u5elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p13_1, u5elo0]
                · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                  linarith only [hlam, p13_0]
            · linarith only [h10, hc45, hlam, hphi, p0_1, u5elo0]
          · linarith only [h9, hc35, hlam, hphi, p0_1, u5elo0]
        · linarith only [h8, hc25, hlam, hphi, p0_1, u5elo0]
      · linarith only [h7, hc15, hlam, hphi, p0_1, u5elo0]
    · linarith only [h6, hlam, p0_0]
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
    rcases p0_3 (m.d 0 5) (by simp) with h60 | h60
    · rcases p0_3 (m.d 1 5) (by simp) with h61 | h61
      · rcases p0_3 (m.d 2 5) (by simp) with h62 | h62
        · rcases p0_3 (m.d 3 5) (by simp) with h63 | h63
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · rcases p0_3 (m.d 5 6) (by simp) with h65 | h65
              · linarith only [h65, hlam, p0_0]
              · rcases h6bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hlam, p67_0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc16, hlam, hphi, p67_1, u6elo0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc26, hlam, hphi, p67_1, u6elo0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc36, hlam, hphi, p67_1, u6elo0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc46, hlam, hphi, p67_1, u6elo0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc56, hlam, hphi, p67_1, u6elo0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc06, hlam, hphi, p67_1, u6elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hlam, p67_0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc26, hlam, hphi, p67_1, u6elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc36, hlam, hphi, p67_1, u6elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc46, hlam, hphi, p67_1, u6elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc56, hlam, hphi, p67_1, u6elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc06, hlam, hphi, p67_1, u6elo2]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc16, hlam, hphi, p67_1, u6elo2]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hlam, p67_0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc36, hlam, hphi, p67_1, u6elo2]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc46, hlam, hphi, p67_1, u6elo2]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc56, hlam, hphi, p67_1, u6elo2]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc06, hlam, hphi, p67_1, u6elo3]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc16, hlam, hphi, p67_1, u6elo3]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc26, hlam, hphi, p67_1, u6elo3]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hlam, p67_0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc46, hlam, hphi, p67_1, u6elo3]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc56, hlam, hphi, p67_1, u6elo3]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc06, hlam, hphi, p67_1, u6elo4]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc16, hlam, hphi, p67_1, u6elo4]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc26, hlam, hphi, p67_1, u6elo4]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc36, hlam, hphi, p67_1, u6elo4]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hlam, p67_0]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc56, hlam, hphi, p67_1, u6elo4]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc06, hlam, hphi, p67_1, u6elo5]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p67_1, u5elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p67_1, u5elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p67_1, u5elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p67_1, u5elo1]
                · obtain ⟨p67_0, p67_1, p67_2, p67_3⟩ := h67c
                  linarith only [hlam, p67_0]
            · linarith only [h64, hc45, hlam, hphi, p0_1, u5elo1]
          · linarith only [h63, hc35, hlam, hphi, p0_1, u5elo1]
        · linarith only [h62, hc25, hlam, hphi, p0_1, u5elo1]
      · linarith only [h61, hlam, p0_0]
    · linarith only [h60, hc05, hlam, hphi, p0_1, u5elo1]
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
    rcases p0_3 (m.d 0 5) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 5) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 5) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 5) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · rcases p0_3 (m.d 5 6) (by simp) with h119 | h119
              · linarith only [h119, hlam, p0_0]
              · rcases h6bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hlam, p121_0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc16, hlam, hphi, p121_1, u6elo0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc26, hlam, hphi, p121_1, u6elo0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc36, hlam, hphi, p121_1, u6elo0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc46, hlam, hphi, p121_1, u6elo0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc56, hlam, hphi, p121_1, u6elo0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc06, hlam, hphi, p121_1, u6elo1]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hlam, p121_0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc26, hlam, hphi, p121_1, u6elo1]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc36, hlam, hphi, p121_1, u6elo1]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc46, hlam, hphi, p121_1, u6elo1]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc56, hlam, hphi, p121_1, u6elo1]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc06, hlam, hphi, p121_1, u6elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc16, hlam, hphi, p121_1, u6elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hlam, p121_0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc36, hlam, hphi, p121_1, u6elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc46, hlam, hphi, p121_1, u6elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc56, hlam, hphi, p121_1, u6elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc06, hlam, hphi, p121_1, u6elo3]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc16, hlam, hphi, p121_1, u6elo3]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc26, hlam, hphi, p121_1, u6elo3]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hlam, p121_0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc46, hlam, hphi, p121_1, u6elo3]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc56, hlam, hphi, p121_1, u6elo3]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc06, hlam, hphi, p121_1, u6elo4]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc16, hlam, hphi, p121_1, u6elo4]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc26, hlam, hphi, p121_1, u6elo4]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc36, hlam, hphi, p121_1, u6elo4]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hlam, p121_0]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc56, hlam, hphi, p121_1, u6elo4]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc06, hlam, hphi, p121_1, u6elo5]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p121_1, u5elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p121_1, u5elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p121_1, u5elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p121_1, u5elo2]
                · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                  linarith only [hlam, p121_0]
            · linarith only [h118, hc45, hlam, hphi, p0_1, u5elo2]
          · linarith only [h117, hc35, hlam, hphi, p0_1, u5elo2]
        · linarith only [h116, hlam, p0_0]
      · linarith only [h115, hc15, hlam, hphi, p0_1, u5elo2]
    · linarith only [h114, hc05, hlam, hphi, p0_1, u5elo2]
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
    rcases p0_3 (m.d 0 5) (by simp) with h168 | h168
    · rcases p0_3 (m.d 1 5) (by simp) with h169 | h169
      · rcases p0_3 (m.d 2 5) (by simp) with h170 | h170
        · rcases p0_3 (m.d 3 5) (by simp) with h171 | h171
          · rcases p0_3 (m.d 4 5) (by simp) with h172 | h172
            · rcases p0_3 (m.d 5 6) (by simp) with h173 | h173
              · linarith only [h173, hlam, p0_0]
              · rcases h6bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hlam, p175_0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc16, hlam, hphi, p175_1, u6elo0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc26, hlam, hphi, p175_1, u6elo0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc36, hlam, hphi, p175_1, u6elo0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc46, hlam, hphi, p175_1, u6elo0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc56, hlam, hphi, p175_1, u6elo0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc06, hlam, hphi, p175_1, u6elo1]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hlam, p175_0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc26, hlam, hphi, p175_1, u6elo1]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc36, hlam, hphi, p175_1, u6elo1]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc46, hlam, hphi, p175_1, u6elo1]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc56, hlam, hphi, p175_1, u6elo1]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc06, hlam, hphi, p175_1, u6elo2]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc16, hlam, hphi, p175_1, u6elo2]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hlam, p175_0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc36, hlam, hphi, p175_1, u6elo2]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc46, hlam, hphi, p175_1, u6elo2]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc56, hlam, hphi, p175_1, u6elo2]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc06, hlam, hphi, p175_1, u6elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc16, hlam, hphi, p175_1, u6elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc26, hlam, hphi, p175_1, u6elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hlam, p175_0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc46, hlam, hphi, p175_1, u6elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc56, hlam, hphi, p175_1, u6elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc06, hlam, hphi, p175_1, u6elo4]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc16, hlam, hphi, p175_1, u6elo4]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc26, hlam, hphi, p175_1, u6elo4]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc36, hlam, hphi, p175_1, u6elo4]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hlam, p175_0]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc56, hlam, hphi, p175_1, u6elo4]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc06, hlam, hphi, p175_1, u6elo5]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p175_1, u5elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p175_1, u5elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p175_1, u5elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p175_1, u5elo3]
                · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                  linarith only [hlam, p175_0]
            · linarith only [h172, hc45, hlam, hphi, p0_1, u5elo3]
          · linarith only [h171, hlam, p0_0]
        · linarith only [h170, hc25, hlam, hphi, p0_1, u5elo3]
      · linarith only [h169, hc15, hlam, hphi, p0_1, u5elo3]
    · linarith only [h168, hc05, hlam, hphi, p0_1, u5elo3]
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 5) (by simp) with h222 | h222
    · rcases p0_3 (m.d 1 5) (by simp) with h223 | h223
      · rcases p0_3 (m.d 2 5) (by simp) with h224 | h224
        · rcases p0_3 (m.d 3 5) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · rcases p0_3 (m.d 5 6) (by simp) with h227 | h227
              · linarith only [h227, hlam, p0_0]
              · rcases h6bigk with h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hlam, p229_0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc16, hlam, hphi, p229_1, u6elo0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc26, hlam, hphi, p229_1, u6elo0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc36, hlam, hphi, p229_1, u6elo0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc46, hlam, hphi, p229_1, u6elo0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc56, hlam, hphi, p229_1, u6elo0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc06, hlam, hphi, p229_1, u6elo1]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hlam, p229_0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc26, hlam, hphi, p229_1, u6elo1]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc36, hlam, hphi, p229_1, u6elo1]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc46, hlam, hphi, p229_1, u6elo1]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc56, hlam, hphi, p229_1, u6elo1]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc06, hlam, hphi, p229_1, u6elo2]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc16, hlam, hphi, p229_1, u6elo2]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hlam, p229_0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc36, hlam, hphi, p229_1, u6elo2]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc46, hlam, hphi, p229_1, u6elo2]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc56, hlam, hphi, p229_1, u6elo2]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc06, hlam, hphi, p229_1, u6elo3]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc16, hlam, hphi, p229_1, u6elo3]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc26, hlam, hphi, p229_1, u6elo3]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hlam, p229_0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc46, hlam, hphi, p229_1, u6elo3]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc56, hlam, hphi, p229_1, u6elo3]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc06, hlam, hphi, p229_1, u6elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc16, hlam, hphi, p229_1, u6elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc26, hlam, hphi, p229_1, u6elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc36, hlam, hphi, p229_1, u6elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hlam, p229_0]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc56, hlam, hphi, p229_1, u6elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc06, hlam, hphi, p229_1, u6elo5]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p229_1, u5elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p229_1, u5elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p229_1, u5elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, p229_1, u5elo4]
                · obtain ⟨p229_0, p229_1, p229_2, p229_3⟩ := h229c
                  linarith only [hlam, p229_0]
            · linarith only [h226, hlam, p0_0]
          · linarith only [h225, hc35, hlam, hphi, p0_1, u5elo4]
        · linarith only [h224, hc25, hlam, hphi, p0_1, u5elo4]
      · linarith only [h223, hc15, hlam, hphi, p0_1, u5elo4]
    · linarith only [h222, hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht56, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
