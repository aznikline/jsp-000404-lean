import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB0_M_IR_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
    · linarith only [h6, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h8 | h8
      · rcases p0_3 (m.d 2 4) (by simp) with h9 | h9
        · rcases p0_3 (m.d 3 4) (by simp) with h10 | h10
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
              · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
                · linarith only [h14, hlam, p0_0]
                · linarith only [h10, h13, h14, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
                · linarith only [h17, hlam, p0_0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
                    · linarith only [h20, h9, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · linarith only [h10, h19, h20, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h23 | h23
                    · linarith only [h19, h23, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h25 | h25
                      · linarith only [h10, h25, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h27, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h11, h27, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h30 | h30
            · linarith only [h30, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
                · linarith only [h33, hlam, p0_0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h36 | h36
                    · linarith only [h32, h33, h36, h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h38 | h38
                      · linarith only [h32, h33, h38, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h10, h38, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
                    · linarith only [h32, h33, h35, h41, h9, hlam, p0_1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
                      · linarith only [h32, h33, h43, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h10, h43, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h46 | h46
                · linarith only [h46, hlam, p0_0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h49 | h49
                    · linarith only [h49, h9, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
                      · linarith only [h48, h49, h51, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h10, h51, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h54 | h54
                    · linarith only [h48, h54, h9, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                        · linarith only [h57, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h30, h57, hlam]
                      · linarith only [h10, h56, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · rcases p0_3 (m.d 4 5) (by simp) with h62 | h62
            · linarith only [h62, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
              · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
                · linarith only [h65, hlam, p0_0]
                · linarith only [h61, h64, h65, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h68 | h68
                · linarith only [h68, hlam, p0_0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h71 | h71
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h72 | h72
                      · linarith only [h61, h71, h72, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h61, h74, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h62, h74, hlam]
                    · linarith only [h71, h9, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h79 | h79
                      · linarith only [h61, h68, h79, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2]
                      · linarith only [h61, h70, h78, h79, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h78, h9, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h85 | h85
              · rcases m.htr 0 1 4 (by decide) (by decide) with h86 | h86
                · linarith only [h86, hlam, p0_0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
                      · linarith only [h85, h86, h90, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h61, h90, hlam]
                    · linarith only [h89, h9, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
                    · linarith only [h85, h86, h88, h94, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h9, h94, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h97 | h97
                · linarith only [h97, hlam, p0_0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h99 | h99
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h100 | h100
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
                        · linarith only [h102, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h102, h83, hlam]
                      · linarith only [h101, h61, hlam]
                    · linarith only [h100, h9, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h109, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h109, h83, hlam]
                      · linarith only [h108, h61, hlam]
                    · linarith only [h107, h9, hlam]
      · linarith only [h8, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
    · linarith only [h116, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
    · rcases p0_3 (m.d 1 4) (by simp) with h118 | h118
      · rcases p0_3 (m.d 2 4) (by simp) with h119 | h119
        · linarith only [h119, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h124 | h124
              · rcases m.htr 0 1 4 (by decide) (by decide) with h125 | h125
                · linarith only [h125, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
                · linarith only [h116, h121, h124, h125, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h128 | h128
                · linarith only [h116, h124, h128, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h131 | h131
                    · linarith only [h116, h131, hlam]
                    · linarith only [h121, h131, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h134 | h134
                    · linarith only [h116, h134, hlam]
                    · linarith only [h121, h134, hc02, hc34, hlam, hphi, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h137 | h137
            · linarith only [h137, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h139 | h139
              · rcases m.htr 0 1 4 (by decide) (by decide) with h140 | h140
                · linarith only [h140, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h143 | h143
                    · linarith only [h116, h143, hlam]
                    · linarith only [h142, h143, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h146 | h146
                    · linarith only [h116, h146, hlam]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
                      · linarith only [h139, h140, h146, h148, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
                        · linarith only [h146, h150, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h137, h140, h150, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
                · linarith only [h139, h153, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h156 | h156
                    · linarith only [h116, h156, hlam]
                    · linarith only [h139, h155, h156, hc01, hc14, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h159 | h159
                    · linarith only [h116, h159, hlam]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h162 | h162
                        · linarith only [h159, h162, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h137, h162, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
                      · linarith only [h121, h139, h161, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h118, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h167 | h167
    · linarith only [h167, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h169 | h169
      · rcases p0_3 (m.d 2 4) (by simp) with h170 | h170
        · rcases p0_3 (m.d 3 4) (by simp) with h171 | h171
          · linarith only [h171, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h173 | h173
            · linarith only [h173, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h175 | h175
              · rcases m.htr 0 1 4 (by decide) (by decide) with h176 | h176
                · linarith only [h176, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h179 | h179
                    · linarith only [h167, h170, h175, h176, h179, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h181 | h181
                      · linarith only [h167, h181, hlam]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h170, h181, h183, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h170, h173, h175, h176, h183, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
                    · linarith only [h170, h178, h186, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h188 | h188
                      · linarith only [h167, h188, hlam]
                      · linarith only [h170, h178, h188, hc02, hc24, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h191 | h191
                · linarith only [h175, h191, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi3]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h194 | h194
                    · linarith only [h167, h170, h191, h194, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h196 | h196
                      · linarith only [h167, h196, hlam]
                      · linarith only [h170, h175, h196, hc01, hc24, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h199 | h199
                    · linarith only [h170, h193, h199, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h201 | h201
                      · linarith only [h167, h201, hlam]
                      · linarith only [h170, h193, h201, hc02, hc24, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h204 | h204
          · linarith only [h204, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h206 | h206
            · linarith only [h170, h206, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h208 | h208
              · rcases m.htr 0 1 4 (by decide) (by decide) with h209 | h209
                · linarith only [h167, h209, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h211 | h211
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h213 | h213
                      · linarith only [h167, h213, hlam]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                        · linarith only [h213, h215, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h206, h215, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
                    · linarith only [h170, h211, h212, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h219 | h219
                    · linarith only [h167, h208, h209, h211, h219, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h221 | h221
                      · linarith only [h167, h221, hlam]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
                        · linarith only [h170, h219, h223, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h206, h209, h223, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h226 | h226
                · linarith only [h170, h208, h226, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h230 | h230
                      · linarith only [h167, h230, hlam]
                      · linarith only [h208, h230, hc01, hc14, hlam, hphi, p0_1]
                    · linarith only [h170, h228, h229, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h234 | h234
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
                      · linarith only [h167, h235, hlam]
                      · linarith only [h228, h234, h235, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h238 | h238
                      · linarith only [h167, h238, hlam]
                      · linarith only [h208, h238, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h169, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h242 | h242
    · linarith only [h242, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi4]
    · rcases p0_3 (m.d 1 4) (by simp) with h244 | h244
      · rcases p0_3 (m.d 2 4) (by simp) with h245 | h245
        · rcases p0_3 (m.d 3 4) (by simp) with h246 | h246
          · rcases p0_3 (m.d 4 5) (by simp) with h247 | h247
            · linarith only [h247, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h249 | h249
              · rcases m.htr 0 1 4 (by decide) (by decide) with h250 | h250
                · linarith only [h250, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi4]
                · linarith only [h242, h246, h249, h250, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h253 | h253
                · linarith only [h242, h249, h253, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h255 | h255
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h256 | h256
                    · linarith only [h242, h245, h253, h256, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · linarith only [h242, h246, h255, h256, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h259 | h259
                    · linarith only [h242, h245, h255, h259, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h261 | h261
                      · linarith only [h242, h246, h261, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                        · linarith only [h242, h263, hlam]
                        · linarith only [h263, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h266 | h266
            · linarith only [h266, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h268 | h268
              · rcases m.htr 0 1 4 (by decide) (by decide) with h269 | h269
                · linarith only [h246, h269, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h272 | h272
                    · linarith only [h242, h245, h268, h269, h272, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h274 | h274
                      · linarith only [h242, h268, h269, h274, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
                        · linarith only [h242, h276, hlam]
                        · linarith only [h245, h269, h276, hc01, hc24, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h279 | h279
                    · linarith only [h245, h246, h271, h279, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
                      · linarith only [h242, h268, h269, h281, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h245, h246, h271, h281, hc02, hc24, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h284 | h284
                · linarith only [h242, h268, h284, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h286 | h286
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h287 | h287
                    · linarith only [h245, h287, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi4]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h289 | h289
                      · linarith only [h242, h286, h287, h289, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h245, h246, h268, h289, hc01, hc24, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
                    · linarith only [h242, h245, h286, h292, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h294 | h294
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
                        · linarith only [h242, h295, hlam]
                        · linarith only [h294, h295, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h245, h246, h268, h294, hc01, hc24, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h299 | h299
          · rcases p0_3 (m.d 4 5) (by simp) with h300 | h300
            · linarith only [h300, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h302 | h302
              · rcases m.htr 0 1 4 (by decide) (by decide) with h303 | h303
                · linarith only [h245, h303, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
                · linarith only [h242, h299, h302, h303, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h306 | h306
                · linarith only [h242, h302, h306, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h310 | h310
                      · linarith only [h242, h299, h309, h310, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                        · linarith only [h242, h312, hlam]
                        · linarith only [h309, h312, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h245, h299, h309, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h317 | h317
                      · linarith only [h242, h299, h306, h317, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2]
                      · linarith only [h242, h299, h308, h316, h317, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h245, h299, h316, hc02, hc34, hlam, hphi, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h321 | h321
            · linarith only [h321, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h323 | h323
              · rcases m.htr 0 1 4 (by decide) (by decide) with h324 | h324
                · linarith only [h242, h324, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h326 | h326
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h327 | h327
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h328 | h328
                      · linarith only [h242, h323, h324, h328, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h330 | h330
                        · linarith only [h242, h330, hlam]
                        · linarith only [h323, h324, h330, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h245, h326, h327, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h334 | h334
                    · linarith only [h242, h323, h324, h326, h334, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h336 | h336
                      · linarith only [h245, h323, h324, h334, h336, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h338 | h338
                        · linarith only [h242, h338, hlam]
                        · linarith only [h324, h338, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h341 | h341
                · linarith only [h245, h323, h341, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h344 | h344
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h345 | h345
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                        · linarith only [h242, h346, hlam]
                        · linarith only [h341, h346, hc01, hc14, hlam, hphi, p0_1]
                      · linarith only [h299, h323, h345, hc01, hc14, hlam, hphi, p0_1]
                    · linarith only [h245, h343, h344, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
                        · linarith only [h242, h353, hlam]
                        · linarith only [h353, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
                      · linarith only [h299, h343, h351, h352, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h357 | h357
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h358 | h358
                        · linarith only [h242, h358, hlam]
                        · linarith only [h358, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
                      · linarith only [h299, h323, h357, hc01, hc14, hlam, hphi, p0_1]
      · linarith only [h244, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h363 | h363
    · linarith only [h363, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h365 | h365
      · rcases p0_3 (m.d 2 4) (by simp) with h366 | h366
        · rcases p0_3 (m.d 3 4) (by simp) with h367 | h367
          · rcases p0_3 (m.d 4 5) (by simp) with h368 | h368
            · linarith only [h368, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h370 | h370
              · rcases m.htr 0 1 4 (by decide) (by decide) with h371 | h371
                · linarith only [h365, h371, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · linarith only [h367, h370, h371, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h374 | h374
                · linarith only [h365, h370, h374, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h377 | h377
                    · linarith only [h377, hlam, p0_0]
                    · linarith only [h367, h376, h377, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h380 | h380
                    · linarith only [h380, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h382 | h382
                      · linarith only [h367, h380, h382, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h384 | h384
                        · linarith only [h365, h384, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h368, h384, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h387 | h387
            · linarith only [h387, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h389 | h389
              · rcases m.htr 0 1 4 (by decide) (by decide) with h390 | h390
                · linarith only [h365, h390, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h393 | h393
                    · linarith only [h393, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
                      · linarith only [h389, h390, h395, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h367, h395, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h398 | h398
                    · linarith only [h398, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
                      · linarith only [h389, h390, h400, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h367, h400, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h403 | h403
                · linarith only [h365, h403, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h405 | h405
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h406 | h406
                    · linarith only [h406, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h408 | h408
                      · linarith only [h405, h406, h408, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h367, h408, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h411 | h411
                    · linarith only [h411, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h413 | h413
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h414 | h414
                        · linarith only [h414, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h387, h414, hlam]
                      · linarith only [h367, h413, hlam]
        · linarith only [h366, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h419 | h419
        · rcases p0_3 (m.d 3 4) (by simp) with h420 | h420
          · rcases p0_3 (m.d 4 5) (by simp) with h421 | h421
            · linarith only [h421, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h423 | h423
              · rcases m.htr 0 1 4 (by decide) (by decide) with h424 | h424
                · rcases m.htr 0 2 3 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h426 | h426
                    · linarith only [h426, hlam, p0_0]
                    · linarith only [h420, h425, h426, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h429 | h429
                    · linarith only [h429, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h431 | h431
                      · linarith only [h420, h424, h431, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi1]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h433 | h433
                        · linarith only [h420, h433, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h421, h433, hlam]
                · linarith only [h365, h424, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h437 | h437
                · rcases m.htr 0 2 3 (by decide) (by decide) with h438 | h438
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h439 | h439
                    · linarith only [h439, hlam, p0_0]
                    · linarith only [h420, h423, h437, h438, h439, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h442 | h442
                    · linarith only [h442, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h444 | h444
                      · linarith only [h420, h444, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                      · linarith only [h420, h423, h437, h444, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h365, h437, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h448 | h448
            · linarith only [h448, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h450 | h450
              · rcases m.htr 0 1 4 (by decide) (by decide) with h451 | h451
                · rcases m.htr 0 2 3 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h453 | h453
                    · linarith only [h453, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h455 | h455
                      · linarith only [h452, h453, h455, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h420, h455, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h458 | h458
                    · linarith only [h458, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h460 | h460
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h461 | h461
                        · linarith only [h461, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h448, h461, hlam]
                      · linarith only [h420, h460, hlam]
                · linarith only [h365, h451, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 2 3 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h468 | h468
                    · linarith only [h468, hlam, p0_0]
                    · linarith only [h450, h466, h467, h468, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h471 | h471
                    · linarith only [h471, hlam, p0_0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h473 | h473
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h474 | h474
                        · linarith only [h474, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h448, h474, hlam]
                      · linarith only [h420, h473, hlam]
                · linarith only [h365, h466, hlam]
        · linarith only [h419, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h480 | h480
    · linarith only [h480, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
    · rcases p0_3 (m.d 1 4) (by simp) with h482 | h482
      · linarith only [h482, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h484 | h484
        · rcases p0_3 (m.d 3 4) (by simp) with h485 | h485
          · rcases p0_3 (m.d 4 5) (by simp) with h486 | h486
            · linarith only [h486, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h488 | h488
              · rcases m.htr 0 1 4 (by decide) (by decide) with h489 | h489
                · linarith only [h480, h489, hlam]
                · linarith only [h488, h489, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h492 | h492
                · linarith only [h480, h492, hlam]
                · linarith only [h485, h492, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h495 | h495
            · linarith only [h495, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h497 | h497
              · rcases m.htr 0 1 4 (by decide) (by decide) with h498 | h498
                · linarith only [h480, h498, hlam]
                · linarith only [h498, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h501 | h501
                · linarith only [h480, h501, hlam]
                · linarith only [h501, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h484, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h506 | h506
    · linarith only [h506, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h508 | h508
      · rcases p0_3 (m.d 2 4) (by simp) with h509 | h509
        · rcases p0_3 (m.d 3 4) (by simp) with h510 | h510
          · linarith only [h510, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h512 | h512
            · linarith only [h512, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h514 | h514
              · rcases m.htr 0 1 4 (by decide) (by decide) with h515 | h515
                · linarith only [h508, h515, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h517 | h517
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h518 | h518
                    · linarith only [h506, h514, h515, h518, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h520 | h520
                      · linarith only [h506, h520, hlam]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h522 | h522
                        · linarith only [h520, h522, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h512, h518, h522, hc02, hc24, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h525 | h525
                    · linarith only [h517, h525, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h527 | h527
                      · linarith only [h506, h527, hlam]
                      · linarith only [h517, h527, hc02, hc24, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h530 | h530
                · linarith only [h508, h514, h530, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi3]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h532 | h532
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h533 | h533
                    · linarith only [h506, h530, h533, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h535 | h535
                      · linarith only [h506, h535, hlam]
                      · linarith only [h514, h535, hc01, hc24, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h538 | h538
                    · linarith only [h532, h538, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h540 | h540
                      · linarith only [h506, h540, hlam]
                      · linarith only [h532, h540, hc02, hc24, hlam, hphi, p0_1]
        · linarith only [h509, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h544 | h544
        · rcases p0_3 (m.d 3 4) (by simp) with h545 | h545
          · linarith only [h545, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h547 | h547
            · linarith only [h508, h547, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h549 | h549
              · rcases m.htr 0 1 4 (by decide) (by decide) with h550 | h550
                · rcases m.htr 0 2 3 (by decide) (by decide) with h551 | h551
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h552 | h552
                    · linarith only [h506, h550, h552, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
                      · linarith only [h506, h554, hlam]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h556 | h556
                        · linarith only [h554, h556, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h547, h556, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi0]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h559 | h559
                    · linarith only [h551, h559, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h561 | h561
                      · linarith only [h506, h561, hlam]
                      · linarith only [h551, h561, hc02, hc24, hlam, hphi, p0_1]
                · linarith only [h508, h550, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h565 | h565
                · rcases m.htr 0 2 3 (by decide) (by decide) with h566 | h566
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h567 | h567
                    · linarith only [h567, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi3]
                    · linarith only [h506, h549, h565, h566, h567, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h570 | h570
                    · linarith only [h506, h570, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h572 | h572
                      · linarith only [h506, h572, hlam]
                      · linarith only [h549, h565, h572, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h508, h565, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h544, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h577 | h577
    · linarith only [h577, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi4]
    · rcases p0_3 (m.d 1 4) (by simp) with h579 | h579
      · rcases p0_3 (m.d 2 4) (by simp) with h580 | h580
        · rcases p0_3 (m.d 3 4) (by simp) with h581 | h581
          · rcases p0_3 (m.d 4 5) (by simp) with h582 | h582
            · linarith only [h582, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h584 | h584
              · rcases m.htr 0 1 4 (by decide) (by decide) with h585 | h585
                · linarith only [h579, h585, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi4]
                · linarith only [h577, h581, h584, h585, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h588 | h588
                · linarith only [h577, h579, h588, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h590 | h590
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h591 | h591
                    · linarith only [h577, h591, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · linarith only [h577, h581, h590, h591, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h594 | h594
                    · linarith only [h577, h588, h594, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
                      · linarith only [h577, h581, h596, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h598 | h598
                        · linarith only [h577, h598, hlam]
                        · linarith only [h598, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h601 | h601
            · linarith only [h601, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h603 | h603
              · rcases m.htr 0 1 4 (by decide) (by decide) with h604 | h604
                · linarith only [h579, h581, h604, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi3]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h606 | h606
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h607 | h607
                    · linarith only [h577, h604, h607, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h609 | h609
                      · linarith only [h577, h603, h604, h609, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h611 | h611
                        · linarith only [h577, h611, hlam]
                        · linarith only [h604, h611, hc01, hc24, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h614 | h614
                    · linarith only [h581, h606, h614, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h616 | h616
                      · linarith only [h577, h579, h603, h604, h616, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h581, h606, h616, hc02, hc24, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h619 | h619
                · linarith only [h577, h579, h603, h619, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h622 | h622
                    · linarith only [h577, h622, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h624 | h624
                      · linarith only [h577, h621, h622, h624, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h581, h603, h624, hc01, hc24, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h627 | h627
                    · linarith only [h577, h627, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h629 | h629
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
                        · linarith only [h577, h630, hlam]
                        · linarith only [h629, h630, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h581, h603, h629, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h580, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h635 | h635
        · rcases p0_3 (m.d 3 4) (by simp) with h636 | h636
          · rcases p0_3 (m.d 4 5) (by simp) with h637 | h637
            · linarith only [h637, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h639 | h639
              · rcases m.htr 0 1 4 (by decide) (by decide) with h640 | h640
                · rcases m.htr 0 2 3 (by decide) (by decide) with h641 | h641
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h642 | h642
                    · linarith only [h577, h642, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · linarith only [h577, h636, h641, h642, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h645 | h645
                    · linarith only [h577, h640, h645, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h647 | h647
                      · linarith only [h577, h636, h640, h647, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi1]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                        · linarith only [h577, h649, hlam]
                        · linarith only [h636, h640, h649, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h579, h636, h640, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h653 | h653
                · rcases m.htr 0 2 3 (by decide) (by decide) with h654 | h654
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h655 | h655
                    · linarith only [h655, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h577, h636, h654, h655, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h658 | h658
                    · linarith only [h577, h658, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h660 | h660
                      · linarith only [h577, h636, h653, h660, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi1]
                      · linarith only [h577, h636, h639, h653, h660, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h579, h636, h653, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h664 | h664
            · linarith only [h664, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h666 | h666
              · rcases m.htr 0 1 4 (by decide) (by decide) with h667 | h667
                · rcases m.htr 0 2 3 (by decide) (by decide) with h668 | h668
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h669 | h669
                    · linarith only [h577, h669, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h671 | h671
                      · linarith only [h577, h668, h669, h671, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h673 | h673
                        · linarith only [h577, h673, hlam]
                        · linarith only [h669, h673, hc02, hc24, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h676 | h676
                    · linarith only [h636, h668, h676, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
                        · linarith only [h577, h679, hlam]
                        · linarith only [h667, h679, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h636, h668, h678, hc02, hc24, hlam, hphi, p0_1]
                · linarith only [h579, h667, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h684 | h684
                · rcases m.htr 0 2 3 (by decide) (by decide) with h685 | h685
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h686 | h686
                    · linarith only [h636, h686, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi3]
                    · linarith only [h577, h666, h684, h685, h686, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h689 | h689
                    · linarith only [h577, h685, h689, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h691 | h691
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h692 | h692
                        · linarith only [h577, h692, hlam]
                        · linarith only [h684, h692, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h636, h666, h684, h691, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h579, h684, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h635, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h698 | h698
    · linarith only [h698, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h700 | h700
      · rcases p0_3 (m.d 2 4) (by simp) with h701 | h701
        · rcases p0_3 (m.d 3 4) (by simp) with h702 | h702
          · rcases p0_3 (m.d 4 5) (by simp) with h703 | h703
            · linarith only [h703, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h705 | h705
              · rcases m.htr 0 1 4 (by decide) (by decide) with h706 | h706
                · linarith only [h700, h706, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · linarith only [h705, h706, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h709 | h709
                · linarith only [h700, h705, h709, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h712 | h712
                    · linarith only [h701, h709, h712, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · linarith only [h711, h712, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h715 | h715
                    · linarith only [h701, h715, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h717 | h717
                      · linarith only [h717, hlam, p0_0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h719 | h719
                        · linarith only [h719, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h703, h719, hlam]
          · linarith only [h702, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h723 | h723
          · rcases p0_3 (m.d 4 5) (by simp) with h724 | h724
            · linarith only [h724, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h726 | h726
              · rcases m.htr 0 1 4 (by decide) (by decide) with h727 | h727
                · linarith only [h700, h701, h727, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
                · linarith only [h726, h727, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h730 | h730
                · linarith only [h700, h730, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h732 | h732
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h733 | h733
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h734 | h734
                      · linarith only [h734, hlam, p0_0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h736 | h736
                        · linarith only [h736, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h724, h736, hlam]
                    · linarith only [h701, h733, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h740 | h740
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h741 | h741
                      · linarith only [h741, hlam, p0_0]
                      · linarith only [h732, h740, h741, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h701, h740, hlam]
          · linarith only [h723, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h746 | h746
        · rcases p0_3 (m.d 3 4) (by simp) with h747 | h747
          · rcases p0_3 (m.d 4 5) (by simp) with h748 | h748
            · linarith only [h748, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h750 | h750
              · rcases m.htr 0 1 4 (by decide) (by decide) with h751 | h751
                · rcases m.htr 0 2 3 (by decide) (by decide) with h752 | h752
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h753 | h753
                    · linarith only [h746, h751, h753, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                    · linarith only [h752, h753, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h756 | h756
                    · linarith only [h746, h751, h756, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h758 | h758
                      · linarith only [h758, hlam, p0_0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
                        · linarith only [h760, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h748, h760, hlam]
                · linarith only [h700, h751, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h764 | h764
                · rcases m.htr 0 2 3 (by decide) (by decide) with h765 | h765
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h766 | h766
                    · linarith only [h746, h766, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · linarith only [h765, h766, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h769 | h769
                    · linarith only [h746, h764, h769, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h771 | h771
                      · linarith only [h771, hlam, p0_0]
                      · linarith only [h750, h764, h771, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h700, h764, hlam]
          · linarith only [h747, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h776 | h776
          · rcases p0_3 (m.d 4 5) (by simp) with h777 | h777
            · linarith only [h777, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h779 | h779
              · rcases m.htr 0 1 4 (by decide) (by decide) with h780 | h780
                · rcases m.htr 0 2 3 (by decide) (by decide) with h781 | h781
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h782 | h782
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h783 | h783
                      · linarith only [h783, hlam, p0_0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h785 | h785
                        · linarith only [h785, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h777, h785, hlam]
                    · linarith only [h746, h782, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h789 | h789
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
                      · linarith only [h790, hlam, p0_0]
                      · linarith only [h781, h789, h790, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h746, h789, hlam]
                · linarith only [h700, h780, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h795 | h795
                · rcases m.htr 0 2 3 (by decide) (by decide) with h796 | h796
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h797 | h797
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h798 | h798
                      · linarith only [h798, hlam, p0_0]
                      · linarith only [h779, h795, h798, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                    · linarith only [h746, h797, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h802 | h802
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h803 | h803
                      · linarith only [h803, hlam, p0_0]
                      · linarith only [h779, h795, h803, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                    · linarith only [h746, h802, hlam]
                · linarith only [h700, h795, hlam]
          · linarith only [h776, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h809 | h809
    · linarith only [h809, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi1]
    · rcases p0_3 (m.d 1 4) (by simp) with h811 | h811
      · linarith only [h811, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h813 | h813
        · rcases p0_3 (m.d 3 4) (by simp) with h814 | h814
          · rcases p0_3 (m.d 4 5) (by simp) with h815 | h815
            · linarith only [h815, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h817 | h817
              · rcases m.htr 0 1 4 (by decide) (by decide) with h818 | h818
                · linarith only [h809, h818, hlam]
                · linarith only [h813, h817, h818, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h821 | h821
                · linarith only [h809, h821, hlam]
                · linarith only [h821, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h814, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h825 | h825
          · rcases p0_3 (m.d 4 5) (by simp) with h826 | h826
            · linarith only [h826, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h828 | h828
              · rcases m.htr 0 1 4 (by decide) (by decide) with h829 | h829
                · linarith only [h809, h829, hlam]
                · linarith only [h828, h829, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h832 | h832
                · linarith only [h809, h832, hlam]
                · linarith only [h832, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h825, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h836 | h836
    · linarith only [h836, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi2]
    · rcases p0_3 (m.d 1 4) (by simp) with h838 | h838
      · rcases p0_3 (m.d 2 4) (by simp) with h839 | h839
        · linarith only [h839, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h841 | h841
          · rcases p0_3 (m.d 4 5) (by simp) with h842 | h842
            · linarith only [h842, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h844 | h844
              · rcases m.htr 0 1 4 (by decide) (by decide) with h845 | h845
                · linarith only [h838, h845, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
                · linarith only [h836, h844, h845, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h848 | h848
                · linarith only [h836, h838, h844, h848, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h851 | h851
                    · linarith only [h836, h851, hlam]
                    · linarith only [h851, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h854 | h854
                    · linarith only [h836, h854, hlam]
                    · linarith only [h854, hc02, hc34, hlam, hphi, ht23, p0_1]
          · linarith only [h841, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h858 | h858
        · linarith only [h858, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h860 | h860
          · rcases p0_3 (m.d 4 5) (by simp) with h861 | h861
            · linarith only [h838, h861, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h863 | h863
              · rcases m.htr 0 1 4 (by decide) (by decide) with h864 | h864
                · rcases m.htr 0 2 3 (by decide) (by decide) with h865 | h865
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h866 | h866
                    · linarith only [h836, h866, hlam]
                    · linarith only [h866, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h869 | h869
                    · linarith only [h836, h869, hlam]
                    · linarith only [h869, hc02, hc34, hlam, hphi, ht23, p0_1]
                · linarith only [h838, h864, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h873 | h873
                · rcases m.htr 0 2 3 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h875 | h875
                    · linarith only [h836, h875, hlam]
                    · linarith only [h875, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h878 | h878
                    · linarith only [h836, h878, hlam]
                    · linarith only [h878, hc02, hc34, hlam, hphi, ht23, p0_1]
                · linarith only [h838, h873, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h860, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h884 | h884
    · linarith only [h884, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo3, u4ehi4]
    · rcases p0_3 (m.d 1 4) (by simp) with h886 | h886
      · rcases p0_3 (m.d 2 4) (by simp) with h887 | h887
        · rcases p0_3 (m.d 3 4) (by simp) with h888 | h888
          · rcases p0_3 (m.d 4 5) (by simp) with h889 | h889
            · linarith only [h889, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h891 | h891
              · rcases m.htr 0 1 4 (by decide) (by decide) with h892 | h892
                · linarith only [h886, h892, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi4]
                · linarith only [h884, h891, h892, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h895 | h895
                · linarith only [h884, h886, h891, h895, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h897 | h897
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h898 | h898
                    · linarith only [h884, h887, h898, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · linarith only [h884, h897, h898, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h901 | h901
                    · linarith only [h884, h887, h895, h901, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h903 | h903
                      · linarith only [h884, h903, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h905 | h905
                        · linarith only [h884, h905, hlam]
                        · linarith only [h886, h905, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi0]
          · linarith only [h888, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h909 | h909
          · rcases p0_3 (m.d 4 5) (by simp) with h910 | h910
            · linarith only [h910, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h912 | h912
              · rcases m.htr 0 1 4 (by decide) (by decide) with h913 | h913
                · linarith only [h886, h887, h913, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi2]
                · linarith only [h884, h912, h913, hc13, hc34, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h916 | h916
                · linarith only [h884, h886, h912, h916, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                · rcases m.htr 0 2 3 (by decide) (by decide) with h918 | h918
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h919 | h919
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h920 | h920
                      · linarith only [h884, h919, h920, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h922 | h922
                        · linarith only [h884, h922, hlam]
                        · linarith only [h919, h922, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h887, h919, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h926 | h926
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h927 | h927
                      · linarith only [h927, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h884, h918, h926, h927, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h887, h926, hc02, hc34, hlam, hphi, ht23, p0_1]
          · linarith only [h909, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h932 | h932
        · rcases p0_3 (m.d 3 4) (by simp) with h933 | h933
          · rcases p0_3 (m.d 4 5) (by simp) with h934 | h934
            · linarith only [h934, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h936 | h936
              · rcases m.htr 0 1 4 (by decide) (by decide) with h937 | h937
                · rcases m.htr 0 2 3 (by decide) (by decide) with h938 | h938
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h939 | h939
                    · linarith only [h884, h932, h939, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                    · linarith only [h884, h938, h939, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h942 | h942
                    · linarith only [h884, h932, h937, h942, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h944 | h944
                      · linarith only [h884, h936, h937, h944, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0, u4ehi1]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
                        · linarith only [h884, h946, hlam]
                        · linarith only [h937, h946, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h886, h937, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h950 | h950
                · rcases m.htr 0 2 3 (by decide) (by decide) with h951 | h951
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h952 | h952
                    · linarith only [h932, h952, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h884, h951, h952, hc23, hc34, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h955 | h955
                    · linarith only [h884, h932, h950, h955, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h957 | h957
                      · linarith only [h884, h950, h957, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi1]
                      · linarith only [h884, h936, h950, h957, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                · linarith only [h886, h950, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h933, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h962 | h962
          · rcases p0_3 (m.d 4 5) (by simp) with h963 | h963
            · linarith only [h963, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h965 | h965
              · rcases m.htr 0 1 4 (by decide) (by decide) with h966 | h966
                · rcases m.htr 0 2 3 (by decide) (by decide) with h967 | h967
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h968 | h968
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h969 | h969
                      · linarith only [h884, h969, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h971 | h971
                        · linarith only [h884, h971, hlam]
                        · linarith only [h968, h971, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h932, h968, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h975 | h975
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h976 | h976
                      · linarith only [h976, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h884, h967, h975, h976, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                    · linarith only [h932, h975, hc02, hc34, hlam, hphi, ht23, p0_1]
                · linarith only [h886, h966, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h981 | h981
                · rcases m.htr 0 2 3 (by decide) (by decide) with h982 | h982
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h983 | h983
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h984 | h984
                      · linarith only [h884, h982, h984, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo1, u4ehi0]
                      · linarith only [h884, h965, h981, h984, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                    · linarith only [h932, h983, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h988 | h988
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h989 | h989
                      · linarith only [h884, h989, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo2, u4ehi0]
                      · linarith only [h884, h965, h981, h989, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                    · linarith only [h932, h988, hc02, hc34, hlam, hphi, ht23, p0_1]
                · linarith only [h886, h981, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h962, hlam, p0_0]
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

set_option maxHeartbeats 3916000 in
theorem n7l_sAB0_M_IR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h0ehi := hb0.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 0 1 4 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h13 | h13
                      · linarith only [h13, h5, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h15 | h15
                        · linarith only [h15, h6, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                                · linarith only [h13, h20, h9, hlam]
                                · linarith only [h15, h19, h20, hc23, hc34, hlam, hphi, p0_1]
                              · linarith only [h12, h13, h19, hc12, hc24, hlam, hphi]
                            · linarith only [h18, h7, hlam, p0_1]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                                · linarith only [h13, h27, h9, hlam]
                                · linarith only [h15, h26, h27, hc23, hc34, hlam, hphi, p0_1]
                              · linarith only [h12, h13, h26, hc12, hc24, hlam, hphi]
                            · linarith only [h25, h7, hlam, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h32 | h32
                      · linarith only [h32, h5, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
                        · linarith only [h34, h6, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h36 | h36
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                              · linarith only [h12, h38, hc12, hlam, hphi, ht01, u0ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                                · linarith only [h32, h40, h9, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
                                  · linarith only [h10, h34, h42, hlam]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                                    · linarith only [h44, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                    · linarith only [h44, h7, hlam]
                            · linarith only [h37, hc45, hlam, hphi, p0_1, u4ehi1]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                              · linarith only [h12, h49, hc12, hlam, hphi, ht01, u0ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                                · linarith only [h32, h51, h9, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                                  · linarith only [h12, h34, h53, hc13, hlam, hphi, ht01, u0ehi1]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                                    · linarith only [h34, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                    · linarith only [h55, h7, hlam]
                            · linarith only [h48, hc45, hlam, hphi, p0_1, u4ehi1]
                  · linarith only [h11, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h60 | h60
                  · linarith only [h10, h60, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h60, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
                · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h64, h9, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h64, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
                  · linarith only [h67, h9, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h67, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h70 | h70
            · linarith only [h70, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h72 | h72
              · rcases m.htr 0 1 3 (by decide) (by decide) with h73 | h73
                · rcases m.htr 0 1 4 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h76 | h76
                      · linarith only [h5, h76, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
                        · linarith only [h75, h76, h78, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                        · linarith only [h6, h74, h78, hc01, hlam, hphi, p0_1, u0ehi2]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h81 | h81
                      · linarith only [h5, h81, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h85 | h85
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                              · linarith only [h72, h75, h83, h86, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                                · linarith only [h72, h75, h81, h88, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                                    · linarith only [h83, h91, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                    · linarith only [h70, h91, hlam]
                                  · linarith only [h6, h90, hlam]
                            · linarith only [h85, hc45, hlam, hphi, p0_1, u4ehi1]
                          · linarith only [h83, h84, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                        · linarith only [h6, h75, h83, hc04, hlam, hphi, p0_1, u0ehi1]
                  · linarith only [h74, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h99 | h99
                  · linarith only [h73, h99, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h99, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h102 | h102
                · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h72, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h103, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
                  · linarith only [h106, h72, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h106, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h109 | h109
          · rcases p0_3 (m.d 4 5) (by simp) with h110 | h110
            · linarith only [h110, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 1 3 (by decide) (by decide) with h113 | h113
                · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h117 | h117
                        · linarith only [h109, h117, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h119 | h119
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                                  · linarith only [h113, h117, h123, hlam]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                                    · linarith only [h117, h125, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                    · linarith only [h110, h125, hlam]
                                · linarith only [h122, h5, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                                · linarith only [h112, h115, h121, h129, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h129, h5, hlam]
                            · linarith only [h120, hc45, hlam, hphi, p0_1, u4ehi1]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                                  · linarith only [h117, h135, h136, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                                    · linarith only [h117, h138, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                                    · linarith only [h110, h138, hlam]
                                · linarith only [h135, h5, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                                · linarith only [h112, h115, h134, h142, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h142, h5, hlam]
                            · linarith only [h133, hc45, hlam, hphi, p0_1, u4ehi1]
                      · linarith only [h116, h5, hc04, hlam, hphi, p0_1, u0ehi1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h147 | h147
                      · linarith only [h115, h147, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h147, h5, hc04, hlam, hphi, p0_1, u0ehi1]
                  · linarith only [h114, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h151 | h151
                  · linarith only [h113, h151, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h151, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h154 | h154
                · rcases m.htr 0 1 4 (by decide) (by decide) with h155 | h155
                  · linarith only [h112, h155, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h155, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h158 | h158
                  · linarith only [h112, h158, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h158, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h161 | h161
            · linarith only [h161, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 1 3 (by decide) (by decide) with h164 | h164
                · rcases m.htr 0 1 4 (by decide) (by decide) with h165 | h165
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h166 | h166
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h167 | h167
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h168 | h168
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h169 | h169
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h170 | h170
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                                    · linarith only [h163, h166, h168, h174, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                    · linarith only [h161, h174, hlam]
                                  · linarith only [h109, h173, hlam]
                                · linarith only [h172, h5, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                                · linarith only [h163, h166, h171, h179, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h179, h5, hlam]
                            · linarith only [h170, hc45, hlam, hphi, p0_1, u4ehi1]
                          · linarith only [h168, h169, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                        · linarith only [h109, h168, hc04, hlam, hphi, p0_1, u0ehi2]
                      · linarith only [h165, h167, h5, hc01, hlam, hphi, p0_1, u0ehi1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
                      · linarith only [h166, h186, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h186, h5, hc04, hlam, hphi, p0_1, u0ehi1]
                  · linarith only [h165, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h190 | h190
                  · linarith only [h164, h190, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h190, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 1 4 (by decide) (by decide) with h194 | h194
                  · linarith only [h163, h194, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h194, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h197 | h197
                  · linarith only [h163, h197, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h197, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h201 | h201
    · rcases p0_3 (m.d 1 4) (by simp) with h202 | h202
      · rcases p0_3 (m.d 2 4) (by simp) with h203 | h203
        · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h205 | h205
          · rcases p0_3 (m.d 4 5) (by simp) with h206 | h206
            · linarith only [h206, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h208 | h208
              · rcases m.htr 0 1 3 (by decide) (by decide) with h209 | h209
                · rcases m.htr 0 1 4 (by decide) (by decide) with h210 | h210
                  · linarith only [h202, h210, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h213 | h213
                      · linarith only [h208, h210, h213, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h213, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h216 | h216
                      · linarith only [h209, h210, h212, h216, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h216, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h219 | h219
                  · linarith only [h202, h219, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h221 | h221
                    · linarith only [h208, h209, h221, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h223 | h223
                      · linarith only [h221, h223, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h223, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h226 | h226
                · rcases m.htr 0 1 4 (by decide) (by decide) with h227 | h227
                  · linarith only [h202, h227, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h231 | h231
                        · linarith only [h205, h231, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
                                  · linarith only [h226, h227, h231, h236, h237, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                                      · linarith only [h226, h227, h235, h237, h240, hlam]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                                        · linarith only [h242, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · linarith only [h206, h242, hlam]
                                    · linarith only [h226, h227, h239, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h208, h231, h236, hc02, hc34, hlam, hphi, ht23, p0_1]
                              · linarith only [h208, h235, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                            · linarith only [h206, h234, hlam, p0_1]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h249 | h249
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h251 | h251
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                                  · linarith only [h226, h227, h231, h251, h252, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h254 | h254
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h255 | h255
                                      · linarith only [h226, h227, h250, h252, h255, hlam]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
                                        · linarith only [h230, h257, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · linarith only [h206, h257, hlam]
                                    · linarith only [h226, h227, h254, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h208, h251, hc04, hlam, hphi, p0_1, u0ehi1]
                              · linarith only [h208, h230, h250, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                            · linarith only [h206, h249, hlam, p0_1]
                      · linarith only [h230, hlam, p0_0]
                    · linarith only [h208, h226, h229, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h266 | h266
                  · linarith only [h202, h266, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h269 | h269
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h270 | h270
                        · linarith only [h205, h270, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h275 | h275
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h276 | h276
                                  · linarith only [h270, h274, h276, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                  · linarith only [h226, h276, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                                · linarith only [h208, h269, h275, hlam, p0_1]
                              · linarith only [h208, h268, h274, hlam]
                            · linarith only [h206, h273, hlam, p0_1]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h282 | h282
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h285 | h285
                                  · linarith only [h270, h285, hc13, hlam, hphi, ht01, u0ehi2]
                                  · linarith only [h226, h285, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                                · linarith only [h208, h269, h284, hlam, p0_1]
                              · linarith only [h208, h268, h269, h283, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                            · linarith only [h206, h282, hlam, p0_1]
                      · linarith only [h269, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
                      · linarith only [h268, h292, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h292, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h295, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h297 | h297
              · rcases m.htr 0 1 3 (by decide) (by decide) with h298 | h298
                · rcases m.htr 0 1 4 (by decide) (by decide) with h299 | h299
                  · linarith only [h202, h299, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h301 | h301
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h302 | h302
                      · linarith only [h297, h299, h302, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h302, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h305 | h305
                      · linarith only [h298, h299, h301, h305, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h305, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h308 | h308
                  · linarith only [h202, h308, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h310 | h310
                    · linarith only [h297, h298, h310, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h312 | h312
                      · linarith only [h297, h298, h312, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h312, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h315 | h315
                · rcases m.htr 0 1 4 (by decide) (by decide) with h316 | h316
                  · linarith only [h202, h316, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h320 | h320
                        · linarith only [h297, h315, h320, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h205, h320, hc04, hlam, hphi, p0_1, u0ehi2]
                      · linarith only [h319, hlam, p0_0]
                    · linarith only [h297, h315, h318, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h325 | h325
                  · linarith only [h202, h325, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h327 | h327
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h328 | h328
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h329 | h329
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h333 | h333
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                                        · linarith only [h327, h329, h337, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · linarith only [h295, h337, hlam]
                                      · linarith only [h205, h336, hlam]
                                    · linarith only [h325, h335, hc45, hlam, hphi, p0_1, u4ehi2]
                                  · linarith only [h205, h315, h334, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
                                · linarith only [h297, h327, h329, h333, hlam, p0_1]
                              · linarith only [h297, h327, h332, hlam]
                            · linarith only [h295, h331, hlam, p0_1]
                          · linarith only [h329, h330, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h205, h329, hc04, hlam, hphi, p0_1, u0ehi2]
                      · linarith only [h328, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h349 | h349
                      · linarith only [h327, h349, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h349, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h352 | h352
        · linarith only [h352, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h354 | h354
          · rcases p0_3 (m.d 4 5) (by simp) with h355 | h355
            · linarith only [h355, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h357 | h357
              · rcases m.htr 0 1 3 (by decide) (by decide) with h358 | h358
                · rcases m.htr 0 1 4 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h361 | h361
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
                        · linarith only [h354, h362, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h364 | h364
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h365 | h365
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h366 | h366
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
                                · linarith only [h202, h367, hlam]
                                · linarith only [h357, h361, h366, h367, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h370 | h370
                                · linarith only [h202, h370, hlam]
                                · linarith only [h362, h370, hc12, hc34, hlam, hphi, ht23, p0_1]
                            · linarith only [h355, h365, hlam, p0_1]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h374 | h374
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
                                · linarith only [h202, h376, hlam]
                                · linarith only [h362, h376, hc12, hc34, hlam, hphi, ht23, p0_1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h379 | h379
                                · linarith only [h202, h379, hlam]
                                · linarith only [h362, h379, hc12, hc34, hlam, hphi, ht23, p0_1]
                            · linarith only [h355, h374, hlam, p0_1]
                      · linarith only [h361, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h384 | h384
                      · linarith only [h360, h384, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h384, hlam, p0_0]
                  · linarith only [h202, h359, hc04, hlam, hphi, p0_1, u0ehi0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h388 | h388
                  · linarith only [h358, h388, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h202, h388, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h391 | h391
                · rcases m.htr 0 1 4 (by decide) (by decide) with h392 | h392
                  · linarith only [h357, h392, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h202, h391, h392, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h395 | h395
                  · linarith only [h357, h395, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h202, h395, hc04, hlam, hphi, p0_1, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h398 | h398
            · linarith only [h202, h398, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h400 | h400
              · rcases m.htr 0 1 3 (by decide) (by decide) with h401 | h401
                · rcases m.htr 0 1 4 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h405 | h405
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h406 | h406
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h407 | h407
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h409 | h409
                                · linarith only [h202, h409, hlam]
                                · linarith only [h400, h403, h405, h408, h409, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                                · linarith only [h202, h412, hlam]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h415 | h415
                                    · linarith only [h400, h403, h405, h412, h415, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                    · linarith only [h398, h400, h403, h405, h415, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
                                    · linarith only [h400, h403, h405, h412, h418, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                    · linarith only [h398, h400, h403, h405, h418, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                            · linarith only [h398, h407, hlam, p0_1]
                          · linarith only [h405, h406, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h354, h405, hc04, hlam, hphi, p0_1, u0ehi2]
                      · linarith only [h404, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h425 | h425
                      · linarith only [h403, h425, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h425, hlam, p0_0]
                  · linarith only [h202, h402, hc04, hlam, hphi, p0_1, u0ehi0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h429 | h429
                  · linarith only [h401, h429, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h202, h429, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h432 | h432
                · rcases m.htr 0 1 4 (by decide) (by decide) with h433 | h433
                  · linarith only [h400, h433, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h202, h432, h433, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h436 | h436
                  · linarith only [h400, h436, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h202, h436, hc04, hlam, hphi, p0_1, u0ehi0]
    · linarith only [h201, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h440 | h440
    · rcases p0_3 (m.d 1 4) (by simp) with h441 | h441
      · rcases p0_3 (m.d 2 4) (by simp) with h442 | h442
        · rcases p0_3 (m.d 3 4) (by simp) with h443 | h443
          · linarith only [h443, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h445 | h445
            · linarith only [h445, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h447 | h447
              · rcases m.htr 0 1 3 (by decide) (by decide) with h448 | h448
                · rcases m.htr 0 1 4 (by decide) (by decide) with h449 | h449
                  · linarith only [h441, h449, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h451 | h451
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h452 | h452
                      · linarith only [h442, h452, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h454 | h454
                        · linarith only [h447, h449, h451, h454, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h454, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h457 | h457
                      · linarith only [h442, h457, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h459 | h459
                        · linarith only [h448, h449, h459, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h459, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h462 | h462
                  · linarith only [h441, h462, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h464 | h464
                    · linarith only [h447, h448, h464, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h466 | h466
                      · linarith only [h442, h466, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h468 | h468
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                              · linarith only [h447, h448, h464, h471, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                                · linarith only [h447, h448, h471, h473, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h475 | h475
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                                        · rcases m.htr 3 4 5 (by decide) (by decide) with h479 | h479
                                          · linarith only [h468, h479, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                          · linarith only [h445, h479, hlam]
                                        · linarith only [h447, h462, h473, h478, hc12, hc45, hlam, hphi, ht23, ht34]
                                      · linarith only [h462, h471, h475, h477, hlam, p0_1]
                                    · linarith only [h445, h462, h476, hlam, p0_1]
                                  · linarith only [h448, h469, h475, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi3]
                            · linarith only [h445, h470, hlam, p0_1]
                          · linarith only [h468, h469, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h468, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h489 | h489
                · rcases m.htr 0 1 4 (by decide) (by decide) with h490 | h490
                  · linarith only [h441, h490, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h492 | h492
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h493 | h493
                      · linarith only [h442, h493, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h495 | h495
                        · linarith only [h447, h489, h495, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h495, hlam, p0_0]
                    · linarith only [h447, h489, h492, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h499 | h499
                  · linarith only [h441, h499, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h501 | h501
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h502 | h502
                      · linarith only [h442, h502, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h504 | h504
                        · linarith only [h501, h502, h504, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h504, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h507 | h507
                      · linarith only [h442, h507, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h509 | h509
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h510 | h510
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h511 | h511
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                              · linarith only [h501, h512, hc12, hlam, hphi, ht01, u0ehi1]
                              · linarith only [h447, h512, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                            · linarith only [h445, h511, hlam, p0_1]
                          · linarith only [h509, h510, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h509, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h518 | h518
          · linarith only [h518, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h520 | h520
            · linarith only [h520, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h522 | h522
              · rcases m.htr 0 1 3 (by decide) (by decide) with h523 | h523
                · rcases m.htr 0 1 4 (by decide) (by decide) with h524 | h524
                  · linarith only [h441, h524, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h526 | h526
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h527 | h527
                      · linarith only [h522, h524, h527, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h442, h526, h527, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h530 | h530
                      · linarith only [h526, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h442, h530, hc04, hlam, hphi, p0_1, u0ehi1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h533 | h533
                  · linarith only [h441, h533, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h535 | h535
                    · linarith only [h522, h523, h535, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h537 | h537
                      · linarith only [h442, h522, h523, h537, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h442, h537, hc04, hlam, hphi, p0_1, u0ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h540 | h540
                · rcases m.htr 0 1 4 (by decide) (by decide) with h541 | h541
                  · linarith only [h441, h541, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h543 | h543
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h544 | h544
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h545 | h545
                        · linarith only [h442, h522, h540, h545, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h545, hlam, p0_0]
                      · linarith only [h442, h544, hc04, hlam, hphi, p0_1, u0ehi1]
                    · linarith only [h522, h540, h543, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h550 | h550
                  · linarith only [h441, h550, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h552 | h552
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h553 | h553
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h555 | h555
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h556 | h556
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h558 | h558
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h559 | h559
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h560 | h560
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                                      · linarith only [h442, h561, hlam]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h563 | h563
                                        · linarith only [h552, h554, h561, h563, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                        · linarith only [h520, h550, h557, h559, h563, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                    · linarith only [h520, h550, h560, hlam, p0_1]
                                  · linarith only [h540, h559, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
                                · linarith only [h522, h552, h554, h558, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                              · linarith only [h522, h552, h554, h557, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                            · linarith only [h520, h556, hlam, p0_1]
                          · linarith only [h554, h555, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h554, hlam, p0_0]
                      · linarith only [h442, h552, h553, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h574 | h574
                      · linarith only [h552, h574, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h442, h574, hc04, hlam, hphi, p0_1, u0ehi1]
      · rcases p0_3 (m.d 2 4) (by simp) with h577 | h577
        · rcases p0_3 (m.d 3 4) (by simp) with h578 | h578
          · linarith only [h578, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h580 | h580
            · linarith only [h441, h580, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h582 | h582
              · rcases m.htr 0 1 3 (by decide) (by decide) with h583 | h583
                · rcases m.htr 0 1 4 (by decide) (by decide) with h584 | h584
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h585 | h585
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h586 | h586
                      · linarith only [h577, h586, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h588 | h588
                        · linarith only [h441, h585, h586, h588, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                        · linarith only [h588, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h591 | h591
                      · linarith only [h577, h591, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h593 | h593
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h594 | h594
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h596 | h596
                              · linarith only [h582, h585, h596, hc01, hlam, hphi, u0ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h598 | h598
                                · linarith only [h441, h582, h591, h598, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h600 | h600
                                  · linarith only [h441, h600, hlam]
                                  · linarith only [h591, h596, h600, hc12, hc24, hlam, hphi, p0_1]
                            · linarith only [h580, h595, hlam, p0_1]
                          · linarith only [h593, h594, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h593, hlam, p0_0]
                  · linarith only [h441, h584, hc04, hlam, hphi, p0_1, u0ehi0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h607 | h607
                  · linarith only [h583, h607, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h441, h607, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h610 | h610
                · rcases m.htr 0 1 4 (by decide) (by decide) with h611 | h611
                  · linarith only [h582, h611, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h441, h610, h611, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h614 | h614
                  · linarith only [h582, h614, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h441, h614, hc04, hlam, hphi, p0_1, u0ehi0]
        · rcases p0_3 (m.d 3 4) (by simp) with h617 | h617
          · linarith only [h617, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h619 | h619
            · linarith only [h441, h619, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h621 | h621
              · rcases m.htr 0 1 3 (by decide) (by decide) with h622 | h622
                · rcases m.htr 0 1 4 (by decide) (by decide) with h623 | h623
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h624 | h624
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h625 | h625
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h626 | h626
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h627 | h627
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h628 | h628
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h631 | h631
                                  · linarith only [h441, h631, hlam]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h633 | h633
                                    · linarith only [h621, h624, h626, h631, h633, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                                    · linarith only [h619, h621, h624, h626, h633, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                · linarith only [h577, h621, h624, h626, h629, h630, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
                                · linarith only [h621, h624, h629, h637, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h639 | h639
                                  · linarith only [h441, h639, hlam]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
                                    · linarith only [h621, h624, h626, h639, h641, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                    · linarith only [h619, h621, h624, h626, h641, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                            · linarith only [h619, h628, hlam, p0_1]
                          · linarith only [h577, h626, h627, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h626, hlam, p0_0]
                      · linarith only [h577, h624, h625, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h648 | h648
                      · linarith only [h624, h648, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h577, h648, hc04, hlam, hphi, p0_1, u0ehi1]
                  · linarith only [h441, h623, hc04, hlam, hphi, p0_1, u0ehi0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h652 | h652
                  · linarith only [h577, h622, h652, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h441, h652, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h655 | h655
                · rcases m.htr 0 1 4 (by decide) (by decide) with h656 | h656
                  · linarith only [h577, h621, h656, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h441, h655, h656, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h659 | h659
                  · linarith only [h621, h659, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h441, h659, hc04, hlam, hphi, p0_1, u0ehi0]
    · linarith only [h440, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h663 | h663
    · rcases p0_3 (m.d 1 4) (by simp) with h664 | h664
      · rcases p0_3 (m.d 2 4) (by simp) with h665 | h665
        · rcases p0_3 (m.d 3 4) (by simp) with h666 | h666
          · rcases p0_3 (m.d 4 5) (by simp) with h667 | h667
            · linarith only [h667, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h669 | h669
              · rcases m.htr 0 1 3 (by decide) (by decide) with h670 | h670
                · rcases m.htr 0 1 4 (by decide) (by decide) with h671 | h671
                  · linarith only [h664, h671, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h673 | h673
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h674 | h674
                      · linarith only [h665, h674, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h676 | h676
                        · linarith only [h666, h676, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h678 | h678
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h680 | h680
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h681 | h681
                                · linarith only [h669, h674, h681, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h683 | h683
                                  · linarith only [h669, h671, h676, h680, h681, h683, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                                  · linarith only [h669, h671, h680, h683, hc23, hc34, hlam, hphi]
                              · linarith only [h673, h674, h680, hc12, hc24, hlam, hphi]
                            · linarith only [h679, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h688 | h688
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h690 | h690
                                · linarith only [h669, h671, h674, h690, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h692 | h692
                                  · linarith only [h669, h671, h676, h689, h690, h692, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                                  · linarith only [h669, h671, h689, h692, hc23, hc34, hlam, hphi]
                              · linarith only [h673, h674, h689, hc12, hc24, hlam, hphi]
                            · linarith only [h688, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h697 | h697
                      · linarith only [h665, h697, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h699 | h699
                        · linarith only [h666, h699, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h701 | h701
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h702 | h702
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h703 | h703
                              · linarith only [h669, h671, h673, h703, hc14, hlam, hphi, ht01, u0ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                                · linarith only [h670, h671, h703, h705, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h707 | h707
                                  · linarith only [h670, h671, h699, h705, h707, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                                      · linarith only [h670, h671, h703, h707, h710, hc12, hc23, hlam, hphi]
                                      · linarith only [h673, h710, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                                    · linarith only [h671, h709, hlam, p0_1]
                            · linarith only [h702, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h716 | h716
                              · linarith only [h673, h716, hc12, hlam, hphi, ht01, u0ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h718 | h718
                                · linarith only [h670, h671, h716, h718, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h720 | h720
                                  · linarith only [h670, h671, h718, h720, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h722 | h722
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h723 | h723
                                      · linarith only [h670, h671, h716, h720, h723, hc12, hc23, hlam, hphi]
                                      · linarith only [h673, h723, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                                    · linarith only [h671, h722, hlam, p0_1]
                            · linarith only [h715, hlam, p0_0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h728 | h728
                  · linarith only [h664, h728, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h730 | h730
                    · linarith only [h669, h670, h730, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h732 | h732
                      · linarith only [h665, h732, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h734 | h734
                        · linarith only [h666, h734, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h736 | h736
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h737 | h737
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h738 | h738
                              · linarith only [h730, h738, hc12, hlam, hphi, ht01, u0ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h740 | h740
                                · linarith only [h669, h670, h734, h740, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h742 | h742
                                  · linarith only [h669, h670, h734, h738, h742, hc12, hc23, hlam, hphi]
                                  · linarith only [h669, h670, h742, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h737, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h746 | h746
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
                              · linarith only [h669, h670, h736, h747, hc23, hc35, hlam, hphi]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h749 | h749
                                · linarith only [h669, h670, h736, h749, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h751 | h751
                                  · linarith only [h669, h670, h734, h747, h751, hc12, hc23, hlam, hphi]
                                  · linarith only [h669, h670, h751, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h746, hlam, p0_0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h755 | h755
                · rcases m.htr 0 1 4 (by decide) (by decide) with h756 | h756
                  · linarith only [h664, h756, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h758 | h758
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h759 | h759
                      · linarith only [h665, h759, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h761 | h761
                        · linarith only [h666, h761, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h763 | h763
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h764 | h764
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h765 | h765
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h766 | h766
                                · linarith only [h759, h766, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                · linarith only [h669, h755, h763, h766, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · linarith only [h669, h755, h763, h765, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · linarith only [h764, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h771 | h771
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
                                · linarith only [h759, h773, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                · linarith only [h669, h773, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                              · linarith only [h669, h755, h772, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · linarith only [h771, hlam, p0_0]
                    · linarith only [h669, h755, h758, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h779 | h779
                  · linarith only [h664, h779, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h781 | h781
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h782 | h782
                      · linarith only [h665, h782, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h784 | h784
                        · linarith only [h666, h784, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h787 | h787
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
                                · linarith only [h782, h789, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                · linarith only [h669, h789, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                              · linarith only [h669, h781, h788, hc02, hlam, hphi, u0ehi0]
                            · linarith only [h787, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h794 | h794
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h795 | h795
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h796 | h796
                                · linarith only [h782, h796, hc12, hlam, hphi, ht01, u0ehi1]
                                · linarith only [h669, h796, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                              · linarith only [h669, h781, h795, hc02, hlam, hphi, u0ehi0]
                            · linarith only [h794, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h801 | h801
                      · linarith only [h665, h801, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h803 | h803
                        · linarith only [h666, h803, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h805 | h805
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h806 | h806
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
                              · linarith only [h781, h807, hc12, hlam, hphi, ht01, u0ehi1]
                              · linarith only [h669, h807, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                            · linarith only [h806, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h811 | h811
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h812 | h812
                              · linarith only [h669, h781, h812, hc12, hlam, hphi, ht01, u0ehi0]
                              · linarith only [h669, h812, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                            · linarith only [h811, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h816 | h816
            · linarith only [h816, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h818 | h818
              · rcases m.htr 0 1 3 (by decide) (by decide) with h819 | h819
                · rcases m.htr 0 1 4 (by decide) (by decide) with h820 | h820
                  · linarith only [h664, h820, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h822 | h822
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h823 | h823
                      · linarith only [h665, h823, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h825 | h825
                        · linarith only [h818, h820, h822, h825, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h666, h825, hc04, hlam, hphi, p0_1, u0ehi2]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h828 | h828
                      · linarith only [h665, h828, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h830 | h830
                        · linarith only [h666, h819, h820, h830, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h666, h822, h830, hc04, hlam, hphi, p0_1, u0ehi1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h833 | h833
                  · linarith only [h664, h833, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h835 | h835
                    · linarith only [h818, h819, h835, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h837 | h837
                      · linarith only [h665, h837, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h841 | h841
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
                              · linarith only [h666, h835, h839, h842, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h844 | h844
                                · linarith only [h666, h818, h837, h844, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h846 | h846
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h847 | h847
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h848 | h848
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h849 | h849
                                        · rcases m.htr 3 4 5 (by decide) (by decide) with h850 | h850
                                          · linarith only [h666, h850, hlam]
                                          · linarith only [h819, h839, h842, h850, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                                        · linarith only [h819, h839, h842, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                                      · linarith only [h818, h833, h842, h846, h848, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h833, h839, h847, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
                                  · linarith only [h666, h819, h839, h846, hlam, p0_1]
                            · linarith only [h841, hlam, p0_0]
                          · linarith only [h666, h839, h840, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h666, h839, hc04, hlam, hphi, p0_1, u0ehi2]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h860 | h860
                · rcases m.htr 0 1 4 (by decide) (by decide) with h861 | h861
                  · linarith only [h664, h861, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h863 | h863
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h864 | h864
                      · linarith only [h665, h864, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h866 | h866
                        · linarith only [h818, h860, h866, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h666, h866, hc04, hlam, hphi, p0_1, u0ehi2]
                    · linarith only [h818, h860, h863, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h870 | h870
                  · linarith only [h664, h870, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h872 | h872
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h873 | h873
                      · linarith only [h665, h873, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
                        · linarith only [h872, h873, h875, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h666, h875, hc04, hlam, hphi, p0_1, u0ehi2]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h878 | h878
                      · linarith only [h665, h878, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h880 | h880
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h881 | h881
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h882 | h882
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h883 | h883
                              · linarith only [h666, h872, h880, h883, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                              · linarith only [h818, h883, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                            · linarith only [h882, hlam, p0_0]
                          · linarith only [h666, h880, h881, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h666, h880, hc04, hlam, hphi, p0_1, u0ehi2]
        · rcases p0_3 (m.d 3 4) (by simp) with h889 | h889
          · rcases p0_3 (m.d 4 5) (by simp) with h890 | h890
            · linarith only [h890, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h892 | h892
              · rcases m.htr 0 1 3 (by decide) (by decide) with h893 | h893
                · rcases m.htr 0 1 4 (by decide) (by decide) with h894 | h894
                  · linarith only [h664, h894, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h897 | h897
                      · linarith only [h892, h894, h897, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h665, h896, h897, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h900 | h900
                      · linarith only [h896, h900, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                      · linarith only [h665, h900, hc04, hlam, hphi, p0_1, u0ehi1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h903 | h903
                  · linarith only [h664, h903, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h905 | h905
                    · linarith only [h892, h893, h905, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h907 | h907
                      · linarith only [h665, h905, h907, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h665, h907, hc04, hlam, hphi, p0_1, u0ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h910 | h910
                · rcases m.htr 0 1 4 (by decide) (by decide) with h911 | h911
                  · linarith only [h664, h911, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h913 | h913
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h915 | h915
                        · linarith only [h889, h915, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h917 | h917
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h918 | h918
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h919 | h919
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h920 | h920
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h921 | h921
                                  · linarith only [h665, h910, h911, h915, h920, h921, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h923 | h923
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h924 | h924
                                      · linarith only [h910, h911, h919, h921, h924, hlam]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
                                        · linarith only [h665, h926, hlam]
                                        · linarith only [h911, h921, h926, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                                    · linarith only [h911, h923, hlam, p0_1]
                                · linarith only [h665, h915, h920, hc12, hc34, hlam, hphi, ht23, p0_1]
                              · linarith only [h892, h914, h919, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                            · linarith only [h918, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h933 | h933
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h934 | h934
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h935 | h935
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h936 | h936
                                  · linarith only [h910, h915, h936, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h938 | h938
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
                                      · linarith only [h910, h911, h934, h936, h939, hlam]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h941 | h941
                                        · linarith only [h665, h941, hlam]
                                        · linarith only [h914, h941, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                    · linarith only [h911, h938, hlam, p0_1]
                                · linarith only [h665, h892, h911, h935, hc14, hlam, hphi, ht01, p0_1, u0ehi1]
                              · linarith only [h665, h892, h914, h934, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                            · linarith only [h933, hlam, p0_0]
                      · linarith only [h665, h913, h914, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h892, h910, h913, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h950 | h950
                  · linarith only [h664, h950, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h952 | h952
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h953 | h953
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h954 | h954
                        · linarith only [h889, h954, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h956 | h956
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h957 | h957
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h958 | h958
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h959 | h959
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                                  · linarith only [h954, h956, h960, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · linarith only [h910, h960, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                                · linarith only [h665, h892, h959, hc04, hlam, hphi, p0_1, u0ehi1]
                              · linarith only [h665, h892, h952, h953, h958, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                            · linarith only [h957, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h966 | h966
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h967 | h967
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h968 | h968
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h969 | h969
                                  · linarith only [h665, h954, h967, h969, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                  · linarith only [h910, h969, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                                · linarith only [h665, h954, h968, hc12, hc34, hlam, hphi, ht23, p0_1]
                              · linarith only [h665, h892, h952, h953, h954, h967, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                            · linarith only [h966, hlam, p0_0]
                      · linarith only [h665, h950, h952, h953, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h976 | h976
                      · linarith only [h952, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                      · linarith only [h665, h976, hc04, hlam, hphi, p0_1, u0ehi1]
          · rcases p0_3 (m.d 4 5) (by simp) with h979 | h979
            · linarith only [h979, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h981 | h981
              · rcases m.htr 0 1 3 (by decide) (by decide) with h982 | h982
                · rcases m.htr 0 1 4 (by decide) (by decide) with h983 | h983
                  · linarith only [h664, h983, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h985 | h985
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h986 | h986
                      · linarith only [h889, h981, h983, h986, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h665, h985, h986, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h989 | h989
                      · linarith only [h985, h989, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                      · linarith only [h665, h989, hc04, hlam, hphi, p0_1, u0ehi1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h992 | h992
                  · linarith only [h664, h992, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h994 | h994
                    · linarith only [h981, h982, h994, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h996 | h996
                      · linarith only [h981, h982, h996, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                      · linarith only [h665, h996, hc04, hlam, hphi, p0_1, u0ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h999 | h999
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h1000, h664, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1002 | h1002
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1003 | h1003
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1004 | h1004
                        · linarith only [h1004, h665, h981, h999, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1004, h889, hc04, hlam, hphi, p0_1, u0ehi2]
                      · linarith only [h1000, h1003, h665, hc14, hlam, hphi, ht01, p0_1, u0ehi1]
                    · linarith only [h1002, h981, h999, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1009 | h1009
                  · linarith only [h1009, h664, hlam]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1011 | h1011
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1012 | h1012
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1013 | h1013
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1014 | h1014
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1015 | h1015
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1016 | h1016
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1017 | h1017
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1018 | h1018
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1019 | h1019
                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1020 | h1020
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1021 | h1021
                                        · linarith only [h1021, h665, hlam]
                                        · linarith only [h1011, h1013, h1021, h981, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1024 | h1024
                                        · linarith only [h1024, h665, hlam]
                                        · linarith only [h1011, h1013, h1024, h981, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                    · linarith only [h1009, h1011, h1013, h1019, h981, hc01, hc12, hlam, hphi, p0_1]
                                  · linarith only [h1011, h1013, h1018, h889, h981, h999, hc12, hlam, hphi, ht01, p0_1, u0ehi0]
                                · linarith only [h1011, h1013, h1017, h889, h981, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                              · linarith only [h1011, h1013, h1016, h889, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                            · linarith only [h1015, hlam, p0_0]
                          · linarith only [h1013, h1014, h889, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h1009, h1013, h889, hc14, hlam, hphi, ht01, p0_1, u0ehi2]
                      · linarith only [h1009, h1011, h1012, h665, h999, hc14, hlam, hphi, ht01, p0_1, u0ehi0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1035 | h1035
                      · linarith only [h1011, h1035, h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1035, h665, hc04, hlam, hphi, p0_1, u0ehi1]
      · rcases p0_3 (m.d 2 4) (by simp) with h1038 | h1038
        · rcases p0_3 (m.d 3 4) (by simp) with h1039 | h1039
          · rcases p0_3 (m.d 4 5) (by simp) with h1040 | h1040
            · linarith only [h1040, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1042 | h1042
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1043 | h1043
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1044 | h1044
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1045 | h1045
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1046 | h1046
                      · linarith only [h1038, h1046, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1048 | h1048
                        · linarith only [h1039, h1048, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1050 | h1050
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1051 | h1051
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1052 | h1052
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1053 | h1053
                                · linarith only [h1042, h1046, h1053, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                                · linarith only [h1048, h1052, h1053, h664, hc23, hc34, hlam, hphi, p0_1]
                              · linarith only [h1045, h1046, h1052, hc12, hc24, hlam, hphi]
                            · linarith only [h1051, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1058 | h1058
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1059 | h1059
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1060 | h1060
                                · linarith only [h1042, h1046, h1060, hlam]
                                · linarith only [h1048, h1059, h1060, h664, hc23, hc34, hlam, hphi, p0_1]
                              · linarith only [h1045, h1046, h1059, hc12, hc24, hlam, hphi]
                            · linarith only [h1058, hlam, p0_0]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1065 | h1065
                      · linarith only [h1038, h1065, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1067 | h1067
                        · linarith only [h1039, h1067, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1069 | h1069
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1070 | h1070
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1071 | h1071
                              · linarith only [h1045, h1071, hc12, hlam, hphi, ht01, u0ehi1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1073 | h1073
                                · linarith only [h1042, h1065, h1073, h664, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1075 | h1075
                                  · linarith only [h1043, h1067, h1075, h664, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1077 | h1077
                                    · linarith only [h1077, h664, hlam]
                                    · linarith only [h1077, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                            · linarith only [h1070, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1081 | h1081
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1082 | h1082
                              · linarith only [h1042, h1045, h1082, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1084 | h1084
                                · linarith only [h1065, h1084, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1086 | h1086
                                  · linarith only [h1043, h1067, h1086, hlam]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1088 | h1088
                                    · linarith only [h1088, h664, hlam]
                                    · linarith only [h1088, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                            · linarith only [h1081, hlam, p0_0]
                  · linarith only [h1039, h1044, h664, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1093 | h1093
                  · linarith only [h1043, h1093, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1093, h664, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1096 | h1096
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1097 | h1097
                  · linarith only [h1042, h1097, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1096, h1097, h664, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1100 | h1100
                  · linarith only [h1096, h1100, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1100, h664, hc04, hlam, hphi, p0_1, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1103 | h1103
            · linarith only [h1103, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1105 | h1105
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1106 | h1106
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1107 | h1107
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1108 | h1108
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1109 | h1109
                      · linarith only [h1038, h1109, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1111 | h1111
                        · linarith only [h1039, h1108, h1109, h1111, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h1039, h1107, h1111, hc01, hlam, hphi, p0_1, u0ehi2]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1114 | h1114
                      · linarith only [h1038, h1114, hlam]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1116 | h1116
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1117 | h1117
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1118 | h1118
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1119 | h1119
                              · linarith only [h1105, h1108, h1119, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1121 | h1121
                                · linarith only [h1105, h1108, h1114, h1121, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1123 | h1123
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1124 | h1124
                                    · linarith only [h1124, h664, hlam]
                                    · linarith only [h1116, h1123, h1124, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                                  · linarith only [h1039, h1108, h1116, h1119, h1123, hc12, hc23, hlam, hphi, p0_1]
                            · linarith only [h1118, hlam, p0_0]
                          · linarith only [h1039, h1116, h1117, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi3]
                        · linarith only [h1039, h1108, h1116, hc04, hlam, hphi, p0_1, u0ehi1]
                  · linarith only [h1038, h1107, h664, hc01, hc24, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1132 | h1132
                  · linarith only [h1039, h1106, h1132, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1132, h664, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1135 | h1135
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1136 | h1136
                  · linarith only [h1105, h1136, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1135, h1136, h664, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1139 | h1139
                  · linarith only [h1105, h1139, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1139, h664, hc04, hlam, hphi, p0_1, u0ehi0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1142 | h1142
          · rcases p0_3 (m.d 4 5) (by simp) with h1143 | h1143
            · linarith only [h1143, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1145 | h1145
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1146 | h1146
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1147 | h1147
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1148 | h1148
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1149 | h1149
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1150 | h1150
                        · linarith only [h1142, h1150, hlam]
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1152 | h1152
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1153 | h1153
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1155 | h1155
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1156 | h1156
                                  · linarith only [h1146, h1150, h1155, h1156, h664, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1158 | h1158
                                    · linarith only [h1158, h664, hlam]
                                    · linarith only [h1145, h1149, h1155, h1158, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                · linarith only [h1038, h1150, h1155, hc12, hc34, hlam, hphi, ht23, p0_1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1162 | h1162
                                · linarith only [h1145, h1148, h1154, h1162, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h1038, h1150, h1162, hc12, hc34, hlam, hphi, ht23, p0_1]
                            · linarith only [h1153, hlam, p0_0]
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1166 | h1166
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1167 | h1167
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1168 | h1168
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1169 | h1169
                                  · linarith only [h1150, h1169, hc13, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1171 | h1171
                                    · linarith only [h1171, h664, hlam]
                                    · linarith only [h1150, h1168, h1171, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                                · linarith only [h1038, h1150, h1168, hc12, hc34, hlam, hphi, ht23, p0_1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1175 | h1175
                                · linarith only [h1145, h1148, h1167, h1175, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h1038, h1150, h1175, hc12, hc34, hlam, hphi, ht23, p0_1]
                            · linarith only [h1166, hlam, p0_0]
                      · linarith only [h1038, h1149, hc04, hlam, hphi, p0_1, u0ehi1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1180 | h1180
                      · linarith only [h1148, h1180, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                      · linarith only [h1038, h1147, h1180, hc01, hlam, hphi, p0_1, u0ehi1]
                  · linarith only [h1142, h1147, h664, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1184 | h1184
                  · linarith only [h1038, h1146, h1184, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1184, h664, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1187 | h1187
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1188 | h1188
                  · linarith only [h1145, h1188, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1187, h1188, h664, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1191 | h1191
                  · linarith only [h1145, h1191, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1191, h664, hc04, hlam, hphi, p0_1, u0ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1194 | h1194
            · linarith only [h1194, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1196 | h1196
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1197 | h1197
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1198 | h1198
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1199 | h1199
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1200 | h1200
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1201 | h1201
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h1202 | h1202
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h1203 | h1203
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h1204 | h1204
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1205 | h1205
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1206 | h1206
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1207 | h1207
                                    · linarith only [h1207, h664, hlam]
                                    · linarith only [h1196, h1199, h1201, h1205, h1207, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1210 | h1210
                                    · linarith only [h1210, h664, hlam]
                                    · linarith only [h1196, h1199, h1201, h1205, h1210, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                                · linarith only [h1038, h1196, h1199, h1201, h1204, h1205, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
                                · linarith only [h1196, h1199, h1204, h1214, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · rcases m.htr 1 3 4 (by decide) (by decide) with h1216 | h1216
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1217 | h1217
                                    · linarith only [h1217, h664, hlam]
                                    · linarith only [h1196, h1199, h1201, h1217, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1220 | h1220
                                    · linarith only [h1220, h664, hlam]
                                    · linarith only [h1196, h1199, h1201, h1220, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                            · linarith only [h1203, hlam, p0_0]
                          · linarith only [h1038, h1201, h1202, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1142, h1196, h1200, h1201, hc01, hlam, hphi, p0_1, u0ehi2]
                      · linarith only [h1038, h1200, hc04, hlam, hphi, p0_1, u0ehi1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1227 | h1227
                      · linarith only [h1142, h1199, h1227, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1038, h1227, hc04, hlam, hphi, p0_1, u0ehi1]
                  · linarith only [h1198, h664, hc04, hlam, hphi, p0_1, u0ehi0]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1231 | h1231
                  · linarith only [h1038, h1197, h1231, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1231, h664, hc04, hlam, hphi, p0_1, u0ehi0]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1234 | h1234
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1235 | h1235
                  · linarith only [h1038, h1196, h1235, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1234, h1235, h664, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1238 | h1238
                  · linarith only [h1142, h1196, h1238, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1238, h664, hc04, hlam, hphi, p0_1, u0ehi0]
    · linarith only [h663, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1244 | h1244
    · rcases p0_3 (m.d 1 4) (by simp) with h1245 | h1245
      · rcases p0_3 (m.d 2 4) (by simp) with h1246 | h1246
        · linarith only [h1246, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1248 | h1248
          · rcases p0_3 (m.d 4 5) (by simp) with h1249 | h1249
            · linarith only [h1249, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1251 | h1251
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1252 | h1252
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1253 | h1253
                  · linarith only [h1253, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1253, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1256 | h1256
                  · linarith only [h1252, h1256, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1256, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1259 | h1259
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1260 | h1260
                  · linarith only [h1260, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1260, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1263 | h1263
                  · linarith only [h1251, h1263, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1263, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h1266 | h1266
            · linarith only [h1266, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1268 | h1268
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1269 | h1269
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1270 | h1270
                  · linarith only [h1270, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1270, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1273 | h1273
                  · linarith only [h1269, h1273, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1273, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1276 | h1276
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1277 | h1277
                  · linarith only [h1277, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1277, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1280 | h1280
                  · linarith only [h1268, h1280, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1244, h1280, hlam]
      · linarith only [h1245, hlam, p0_0]
    · linarith only [h1244, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1285 | h1285
    · rcases p0_3 (m.d 1 4) (by simp) with h1286 | h1286
      · rcases p0_3 (m.d 2 4) (by simp) with h1287 | h1287
        · rcases p0_3 (m.d 3 4) (by simp) with h1288 | h1288
          · linarith only [h1288, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1290 | h1290
            · linarith only [h1290, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1292 | h1292
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1293 | h1293
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1294 | h1294
                  · linarith only [h1294, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1294, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1297 | h1297
                  · linarith only [h1293, h1297, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1297, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1300 | h1300
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1301 | h1301
                  · linarith only [h1301, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1301, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1304 | h1304
                  · linarith only [h1292, h1304, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1304, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h1307 | h1307
          · linarith only [h1307, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1309 | h1309
            · linarith only [h1309, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1311 | h1311
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1312 | h1312
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1313 | h1313
                  · linarith only [h1313, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1313, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1316 | h1316
                  · linarith only [h1312, h1316, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1316, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1319 | h1319
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1320 | h1320
                  · linarith only [h1320, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1320, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1323 | h1323
                  · linarith only [h1311, h1323, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1285, h1323, hlam]
      · linarith only [h1286, hlam, p0_0]
    · linarith only [h1285, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1328 | h1328
    · rcases p0_3 (m.d 1 4) (by simp) with h1329 | h1329
      · rcases p0_3 (m.d 2 4) (by simp) with h1330 | h1330
        · rcases p0_3 (m.d 3 4) (by simp) with h1331 | h1331
          · rcases p0_3 (m.d 4 5) (by simp) with h1332 | h1332
            · linarith only [h1332, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1334 | h1334
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1335 | h1335
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1336 | h1336
                  · linarith only [h1336, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1328, h1336, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1339 | h1339
                  · linarith only [h1335, h1339, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1339, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1342 | h1342
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1343 | h1343
                  · linarith only [h1343, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1343, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1346 | h1346
                  · linarith only [h1334, h1346, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1346, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h1349 | h1349
            · linarith only [h1349, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1351 | h1351
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1352 | h1352
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1353 | h1353
                  · linarith only [h1353, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1353, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1356 | h1356
                  · linarith only [h1352, h1356, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1356, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1359 | h1359
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1360 | h1360
                  · linarith only [h1360, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1360, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1363 | h1363
                  · linarith only [h1351, h1363, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1363, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h1366 | h1366
          · rcases p0_3 (m.d 4 5) (by simp) with h1367 | h1367
            · linarith only [h1367, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1369 | h1369
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1370 | h1370
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1371 | h1371
                  · linarith only [h1371, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1371, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1374 | h1374
                  · linarith only [h1370, h1374, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1374, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1377 | h1377
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1378 | h1378
                  · linarith only [h1378, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1378, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1381 | h1381
                  · linarith only [h1369, h1381, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1381, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h1384 | h1384
            · linarith only [h1384, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1386 | h1386
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1387 | h1387
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1388 | h1388
                  · linarith only [h1388, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1388, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1391 | h1391
                  · linarith only [h1387, h1391, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1391, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1394 | h1394
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1395 | h1395
                  · linarith only [h1395, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1395, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1398 | h1398
                  · linarith only [h1386, h1398, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · linarith only [h1328, h1398, hlam]
      · linarith only [h1329, hlam, p0_0]
    · linarith only [h1328, hc14, hlam, hphi, ht01, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1404 | h1404
    · rcases p0_3 (m.d 1 4) (by simp) with h1405 | h1405
      · linarith only [h1405, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1407 | h1407
        · rcases p0_3 (m.d 3 4) (by simp) with h1408 | h1408
          · rcases p0_3 (m.d 4 5) (by simp) with h1409 | h1409
            · linarith only [h1409, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1411 | h1411
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1412 | h1412
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1413 | h1413
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1414 | h1414
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1415 | h1415
                      · linarith only [h1411, h1415, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h1404, h1415, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1418 | h1418
                      · linarith only [h1414, h1418, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h1404, h1418, hlam]
                  · linarith only [h1413, hc01, hc24, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1422 | h1422
                  · linarith only [h1404, h1412, h1422, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1422, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1425 | h1425
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1426 | h1426
                  · linarith only [h1404, h1411, h1426, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1404, h1425, h1426, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1429 | h1429
                  · linarith only [h1404, h1411, h1429, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1429, hc01, hc24, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h1432 | h1432
            · linarith only [h1432, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1434 | h1434
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1435 | h1435
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1436 | h1436
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1437 | h1437
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1438 | h1438
                      · linarith only [h1438, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h1404, h1438, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1441 | h1441
                      · linarith only [h1441, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h1404, h1441, hlam]
                  · linarith only [h1436, hc01, hc24, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1445 | h1445
                  · linarith only [h1404, h1435, h1445, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1445, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1448 | h1448
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1449 | h1449
                  · linarith only [h1404, h1434, h1449, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1404, h1448, h1449, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1452 | h1452
                  · linarith only [h1404, h1434, h1452, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1452, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h1407, hlam, p0_0]
    · linarith only [h1404, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1458 | h1458
    · rcases p0_3 (m.d 1 4) (by simp) with h1459 | h1459
      · rcases p0_3 (m.d 2 4) (by simp) with h1460 | h1460
        · rcases p0_3 (m.d 3 4) (by simp) with h1461 | h1461
          · linarith only [h1461, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1463 | h1463
            · linarith only [h1463, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1465 | h1465
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1466 | h1466
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1467 | h1467
                  · linarith only [h1459, h1467, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1469 | h1469
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1470 | h1470
                      · linarith only [h1465, h1467, h1470, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1470, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1473 | h1473
                      · linarith only [h1466, h1467, h1469, h1473, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1473, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1476 | h1476
                  · linarith only [h1459, h1476, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1478 | h1478
                    · linarith only [h1465, h1466, h1478, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1480 | h1480
                      · linarith only [h1465, h1466, h1480, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1480, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1483 | h1483
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1484 | h1484
                  · linarith only [h1459, h1484, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1486 | h1486
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1487 | h1487
                      · linarith only [h1465, h1487, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1487, hlam]
                    · linarith only [h1465, h1483, h1486, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1491 | h1491
                  · linarith only [h1459, h1491, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1493 | h1493
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1494 | h1494
                      · linarith only [h1465, h1494, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1494, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1497 | h1497
                      · linarith only [h1493, h1497, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1497, hlam]
        · linarith only [h1460, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1501 | h1501
        · rcases p0_3 (m.d 3 4) (by simp) with h1502 | h1502
          · linarith only [h1502, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1504 | h1504
            · linarith only [h1504, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1506 | h1506
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1507 | h1507
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1508 | h1508
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1509 | h1509
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1510 | h1510
                      · linarith only [h1506, h1510, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1510, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1513 | h1513
                      · linarith only [h1509, h1513, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1458, h1513, hlam]
                  · linarith only [h1459, h1508, hc01, hc24, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1517 | h1517
                  · linarith only [h1458, h1507, h1517, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1459, h1517, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1520 | h1520
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1521 | h1521
                  · linarith only [h1458, h1506, h1521, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1458, h1459, h1520, h1521, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1524 | h1524
                  · linarith only [h1458, h1506, h1524, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi3]
                  · linarith only [h1459, h1524, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h1501, hlam, p0_0]
    · linarith only [h1458, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1529 | h1529
    · rcases p0_3 (m.d 1 4) (by simp) with h1530 | h1530
      · rcases p0_3 (m.d 2 4) (by simp) with h1531 | h1531
        · rcases p0_3 (m.d 3 4) (by simp) with h1532 | h1532
          · rcases p0_3 (m.d 4 5) (by simp) with h1533 | h1533
            · linarith only [h1533, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1535 | h1535
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1536 | h1536
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1537 | h1537
                  · linarith only [h1530, h1537, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1539 | h1539
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1540 | h1540
                      · linarith only [h1540, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1540, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1543 | h1543
                      · linarith only [h1536, h1537, h1539, h1543, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1543, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1546 | h1546
                  · linarith only [h1530, h1546, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1548 | h1548
                    · linarith only [h1535, h1536, h1548, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1550 | h1550
                      · linarith only [h1535, h1536, h1550, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1550, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1553 | h1553
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1554 | h1554
                  · linarith only [h1530, h1554, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1556 | h1556
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1557 | h1557
                      · linarith only [h1535, h1557, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1557, hlam]
                    · linarith only [h1535, h1553, h1556, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1561 | h1561
                  · linarith only [h1530, h1561, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1563 | h1563
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1564 | h1564
                      · linarith only [h1535, h1564, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1564, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1567 | h1567
                      · linarith only [h1563, h1567, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1567, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h1570 | h1570
            · linarith only [h1570, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1572 | h1572
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1573 | h1573
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1574 | h1574
                  · linarith only [h1530, h1574, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1576 | h1576
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1577 | h1577
                      · linarith only [h1572, h1574, h1577, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1577, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1580 | h1580
                      · linarith only [h1573, h1574, h1576, h1580, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1580, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1583 | h1583
                  · linarith only [h1530, h1583, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1585 | h1585
                    · linarith only [h1572, h1573, h1585, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1587 | h1587
                      · linarith only [h1572, h1573, h1587, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1587, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1590 | h1590
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1591 | h1591
                  · linarith only [h1530, h1591, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1593 | h1593
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1594 | h1594
                      · linarith only [h1572, h1594, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1594, hlam]
                    · linarith only [h1572, h1590, h1593, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1598 | h1598
                  · linarith only [h1530, h1598, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1600 | h1600
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1601 | h1601
                      · linarith only [h1572, h1601, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1601, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1604 | h1604
                      · linarith only [h1600, h1604, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1604, hlam]
        · linarith only [h1531, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1608 | h1608
        · rcases p0_3 (m.d 3 4) (by simp) with h1609 | h1609
          · rcases p0_3 (m.d 4 5) (by simp) with h1610 | h1610
            · linarith only [h1610, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1612 | h1612
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1613 | h1613
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1614 | h1614
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1615 | h1615
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1616 | h1616
                      · linarith only [h1612, h1616, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1616, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1619 | h1619
                      · linarith only [h1615, h1619, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1529, h1619, hlam]
                  · linarith only [h1530, h1614, hc01, hc24, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1623 | h1623
                  · linarith only [h1529, h1530, h1613, h1623, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1529, h1530, h1612, h1623, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1626 | h1626
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1627 | h1627
                  · linarith only [h1529, h1612, h1627, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1529, h1530, h1626, h1627, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1630 | h1630
                  · linarith only [h1529, h1612, h1630, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1530, h1630, hc01, hc24, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h1633 | h1633
            · linarith only [h1633, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1635 | h1635
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1636 | h1636
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1637 | h1637
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1638 | h1638
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1639 | h1639
                      · linarith only [h1609, h1639, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1529, h1639, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1642 | h1642
                      · linarith only [h1609, h1638, h1642, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi3]
                      · linarith only [h1529, h1642, hlam]
                  · linarith only [h1530, h1637, hc01, hc24, hlam, hphi, ht12, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1646 | h1646
                  · linarith only [h1529, h1530, h1636, h1646, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1529, h1530, h1635, h1646, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1649 | h1649
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1650 | h1650
                  · linarith only [h1529, h1635, h1650, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1529, h1530, h1649, h1650, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1653 | h1653
                  · linarith only [h1529, h1635, h1653, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1530, h1653, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h1608, hlam, p0_0]
    · linarith only [h1529, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1659 | h1659
    · rcases p0_3 (m.d 1 4) (by simp) with h1660 | h1660
      · linarith only [h1660, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1662 | h1662
        · rcases p0_3 (m.d 3 4) (by simp) with h1663 | h1663
          · rcases p0_3 (m.d 4 5) (by simp) with h1664 | h1664
            · linarith only [h1664, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1666 | h1666
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1667 | h1667
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1668 | h1668
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1669 | h1669
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1670 | h1670
                      · linarith only [h1662, h1670, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1672 | h1672
                        · linarith only [h1672, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                        · linarith only [h1659, h1672, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1675 | h1675
                      · linarith only [h1662, h1675, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1677 | h1677
                        · linarith only [h1669, h1677, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                        · linarith only [h1659, h1677, hlam]
                  · linarith only [h1668, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1681 | h1681
                  · linarith only [h1659, h1667, h1681, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1681, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1684 | h1684
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1685 | h1685
                  · linarith only [h1659, h1666, h1685, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1659, h1684, h1685, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1688 | h1688
                  · linarith only [h1659, h1666, h1688, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1688, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1663, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1692 | h1692
          · rcases p0_3 (m.d 4 5) (by simp) with h1693 | h1693
            · linarith only [h1693, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1695 | h1695
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1696 | h1696
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1697 | h1697
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1698 | h1698
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1699 | h1699
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1700 | h1700
                        · linarith only [h1700, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                        · linarith only [h1659, h1700, hlam]
                      · linarith only [h1662, h1699, hc02, hc34, hlam, hphi, ht23, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1704 | h1704
                      · linarith only [h1659, h1698, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h1662, h1695, h1704, hc12, hc34, hlam, hphi, ht23, p0_1]
                  · linarith only [h1697, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1708 | h1708
                  · linarith only [h1659, h1696, h1708, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1708, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1711 | h1711
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1712 | h1712
                  · linarith only [h1659, h1695, h1712, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1659, h1711, h1712, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1715 | h1715
                  · linarith only [h1659, h1695, h1715, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1715, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1692, hlam, p0_0]
    · linarith only [h1659, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1720 | h1720
    · rcases p0_3 (m.d 1 4) (by simp) with h1721 | h1721
      · rcases p0_3 (m.d 2 4) (by simp) with h1722 | h1722
        · linarith only [h1722, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1724 | h1724
          · rcases p0_3 (m.d 4 5) (by simp) with h1725 | h1725
            · linarith only [h1725, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1727 | h1727
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1728 | h1728
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1729 | h1729
                  · linarith only [h1721, h1729, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1731 | h1731
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1732 | h1732
                      · linarith only [h1720, h1727, h1729, h1732, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h1720, h1731, h1732, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1735 | h1735
                      · linarith only [h1720, h1731, h1735, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h1735, hc02, hc34, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1738 | h1738
                  · linarith only [h1721, h1738, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1740 | h1740
                    · linarith only [h1727, h1728, h1740, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1742 | h1742
                      · linarith only [h1720, h1727, h1728, h1742, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h1742, hc02, hc34, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1745 | h1745
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1746 | h1746
                  · linarith only [h1721, h1746, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1748 | h1748
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1749 | h1749
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1750 | h1750
                        · linarith only [h1727, h1745, h1750, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1720, h1750, hlam]
                      · linarith only [h1749, hc02, hc34, hlam, hphi, ht23, p0_1]
                    · linarith only [h1727, h1745, h1748, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1755 | h1755
                  · linarith only [h1721, h1755, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1757 | h1757
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1758 | h1758
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1759 | h1759
                        · linarith only [h1727, h1757, h1759, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1720, h1759, hlam]
                      · linarith only [h1757, h1758, hc23, hc34, hlam, hphi, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1763 | h1763
                      · linarith only [h1720, h1757, h1763, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h1727, h1763, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1724, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1767 | h1767
        · linarith only [h1767, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1769 | h1769
          · rcases p0_3 (m.d 4 5) (by simp) with h1770 | h1770
            · linarith only [h1721, h1770, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1772 | h1772
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1773 | h1773
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1774 | h1774
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1775 | h1775
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1776 | h1776
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1777 | h1777
                        · linarith only [h1777, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1720, h1777, hlam]
                      · linarith only [h1776, hc02, hc34, hlam, hphi, ht23, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1781 | h1781
                      · linarith only [h1720, h1721, h1775, h1781, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h1781, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · linarith only [h1721, h1774, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1785 | h1785
                  · linarith only [h1720, h1773, h1785, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1721, h1785, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1788 | h1788
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1789 | h1789
                  · linarith only [h1720, h1721, h1772, h1789, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1720, h1721, h1788, h1789, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1792 | h1792
                  · linarith only [h1720, h1772, h1792, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1721, h1792, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1769, hlam, p0_0]
    · linarith only [h1720, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h1798 | h1798
    · rcases p0_3 (m.d 1 4) (by simp) with h1799 | h1799
      · rcases p0_3 (m.d 2 4) (by simp) with h1800 | h1800
        · rcases p0_3 (m.d 3 4) (by simp) with h1801 | h1801
          · rcases p0_3 (m.d 4 5) (by simp) with h1802 | h1802
            · linarith only [h1802, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1804 | h1804
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1805 | h1805
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1806 | h1806
                  · linarith only [h1799, h1806, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1808 | h1808
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1809 | h1809
                      · linarith only [h1800, h1809, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1811 | h1811
                        · linarith only [h1811, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h1798, h1811, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1814 | h1814
                      · linarith only [h1800, h1805, h1806, h1808, h1814, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1816 | h1816
                        · linarith only [h1805, h1806, h1816, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h1798, h1816, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1819 | h1819
                  · linarith only [h1799, h1819, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1821 | h1821
                    · linarith only [h1804, h1805, h1821, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1823 | h1823
                      · linarith only [h1800, h1804, h1805, h1823, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1825 | h1825
                        · linarith only [h1825, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h1798, h1825, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1828 | h1828
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1829 | h1829
                  · linarith only [h1799, h1829, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1831 | h1831
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1832 | h1832
                      · linarith only [h1800, h1804, h1832, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1834 | h1834
                        · linarith only [h1804, h1828, h1832, h1834, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h1798, h1834, hlam]
                    · linarith only [h1804, h1828, h1831, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1838 | h1838
                  · linarith only [h1799, h1838, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1840 | h1840
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1841 | h1841
                      · linarith only [h1800, h1804, h1841, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1843 | h1843
                        · linarith only [h1840, h1841, h1843, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h1798, h1843, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1846 | h1846
                      · linarith only [h1800, h1846, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1848 | h1848
                        · linarith only [h1840, h1848, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h1798, h1848, hlam]
          · linarith only [h1801, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1852 | h1852
          · rcases p0_3 (m.d 4 5) (by simp) with h1853 | h1853
            · linarith only [h1853, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1855 | h1855
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1856 | h1856
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1857 | h1857
                  · linarith only [h1799, h1857, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1859 | h1859
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1860 | h1860
                      · linarith only [h1798, h1855, h1857, h1860, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · linarith only [h1798, h1800, h1859, h1860, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1863 | h1863
                      · linarith only [h1798, h1859, h1863, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                      · linarith only [h1800, h1863, hc02, hc34, hlam, hphi, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1866 | h1866
                  · linarith only [h1799, h1800, h1866, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1868 | h1868
                    · linarith only [h1855, h1856, h1868, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1870 | h1870
                      · linarith only [h1798, h1800, h1868, h1870, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h1800, h1870, hc02, hc34, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1873 | h1873
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1874 | h1874
                  · linarith only [h1799, h1800, h1874, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1876 | h1876
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1877 | h1877
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1878 | h1878
                        · linarith only [h1800, h1855, h1873, h1878, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1798, h1878, hlam]
                      · linarith only [h1800, h1877, hc02, hc34, hlam, hphi, ht23, p0_1]
                    · linarith only [h1855, h1873, h1876, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1883 | h1883
                  · linarith only [h1799, h1800, h1883, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1885 | h1885
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1886 | h1886
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1887 | h1887
                        · linarith only [h1800, h1887, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1798, h1887, hlam]
                      · linarith only [h1800, h1886, hc02, hc34, hlam, hphi, ht23, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1891 | h1891
                      · linarith only [h1798, h1800, h1885, h1891, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi2]
                      · linarith only [h1800, h1855, h1891, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1852, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1895 | h1895
        · rcases p0_3 (m.d 3 4) (by simp) with h1896 | h1896
          · rcases p0_3 (m.d 4 5) (by simp) with h1897 | h1897
            · linarith only [h1897, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1899 | h1899
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1900 | h1900
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1901 | h1901
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1902 | h1902
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1903 | h1903
                      · linarith only [h1895, h1903, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1905 | h1905
                        · linarith only [h1905, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
                        · linarith only [h1798, h1905, hlam]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1908 | h1908
                      · linarith only [h1895, h1908, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi4]
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1910 | h1910
                        · linarith only [h1902, h1910, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h1798, h1910, hlam]
                  · linarith only [h1799, h1901, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1914 | h1914
                  · linarith only [h1798, h1799, h1900, h1914, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h1798, h1799, h1899, h1914, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1917 | h1917
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1918 | h1918
                  · linarith only [h1798, h1899, h1918, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1798, h1799, h1917, h1918, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1921 | h1921
                  · linarith only [h1798, h1899, h1921, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1799, h1921, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1896, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h1925 | h1925
          · rcases p0_3 (m.d 4 5) (by simp) with h1926 | h1926
            · linarith only [h1926, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1928 | h1928
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1929 | h1929
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1930 | h1930
                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1931 | h1931
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1932 | h1932
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h1933 | h1933
                        · linarith only [h1895, h1933, hc03, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi2]
                        · linarith only [h1798, h1933, hlam]
                      · linarith only [h1895, h1932, hc02, hc34, hlam, hphi, ht23, p0_1]
                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1937 | h1937
                      · linarith only [h1798, h1799, h1931, h1937, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u4ehi1]
                      · linarith only [h1895, h1928, h1937, hc12, hc34, hlam, hphi, ht23, p0_1]
                  · linarith only [h1799, h1930, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1941 | h1941
                  · linarith only [h1798, h1895, h1929, h1941, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u4ehi2]
                  · linarith only [h1799, h1941, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h1944 | h1944
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1945 | h1945
                  · linarith only [h1798, h1928, h1945, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1798, h1799, h1944, h1945, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h1948 | h1948
                  · linarith only [h1798, h1928, h1948, hc12, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
                  · linarith only [h1799, h1948, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h1925, hlam, p0_0]
    · linarith only [h1798, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
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

theorem n7l_sAB0_M_IR_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
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
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
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
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h15, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                                  · linarith only [h0, h17, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                                    · linarith only [h0, h12, h15, h19, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                    · linarith only [h19, hlam, hphi, ht45, u4ehi2, u5elo4]
                              · linarith only [h14, h8, hlam, hphi, ht45, u4ehi1, u5elo0]
                            · linarith only [h12, h13, h7, hlam, hphi, ht45, u4ehi3, u5elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h12, h24, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                                · linarith only [h0, h27, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                                  · linarith only [h24, h29, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                    · linarith only [h0, h10, h31, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h31, hlam, hphi, ht45, u4ehi2, u5elo4]
                              · linarith only [h26, h8, hlam, hphi, ht45, u4ehi1, u5elo0]
                        · linarith only [h11, h5, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h0, h10, h36, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                        · linarith only [h36, h5, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                      · linarith only [h0, h3, h39, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                        · linarith only [h0, h3, h41, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                                      · linarith only [h1, h43, h49, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h49, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h0, h3, h43, h45, h48, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                  · linarith only [h44, h47, h9, hlam]
                                · linarith only [h0, h3, h44, h46, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · linarith only [h45, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h43, h44, hlam, hphi, ht45, u4ehi3, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                            · linarith only [h0, h3, h43, h57, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                                · linarith only [h0, h3, h43, h59, h60, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                                  · linarith only [h57, h60, h62, hc13, hc34, hlam, hphi]
                                  · linarith only [h62, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h59, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h8, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h6, h7, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 4 5 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                          · linarith only [h6, h68, h73, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                                · linarith only [h1, h6, h75, h77, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                                  · linarith only [h0, h71, h77, h79, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                                  · linarith only [h1, h6, h75, h79, hc23, hc34, hlam, hphi]
                              · linarith only [h76, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h6, h68, h75, hc13, hc34, hlam, hphi]
                        · linarith only [h5, h70, h72, hc23, hlam, hphi, ht34, ht45, u5elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h0, h4, h71, h85, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                        · linarith only [h5, h70, h85, hc23, hlam, hphi, ht34, ht45, u5elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                      · linarith only [h0, h3, h70, h88, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                        · linarith only [h3, h6, h70, h90, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                          · linarith only [h3, h6, h70, h92, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                                · linarith only [h3, h6, h96, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                                      · rcases h4bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h100, h92, h94, hc04, hlam, hphi, ht0b, ht45, ht5b, p101_1, u4ehi4]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h0, h100, h4, h88, h92, h94, hc01, hlam, hphi, ht0b, ht45, ht5b, p101_1, u4ehi4]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h6, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          rcases p101_3 (m.d 0 4) (by simp) with h106 | h106
                                          · rcases p101_3 (m.d 1 4) (by simp) with h107 | h107
                                            · linarith only [h107, h2, hlam]
                                            · linarith only [h107, h95, hlam]
                                          · linarith only [h106, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h2, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h88, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h92, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p101_1, u4ehi4]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h4, hlam, p101_1]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p101_1, u4ehi1]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h96, hlam, p101_1]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p101_1, u4ehi4]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h100, h2, h92, h94, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p101_1, u4ehi4]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h100, h92, h94, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p101_1, u4ehi4]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h88, hc12, hc34, hlam, hphi, ht23, p101_1]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          rcases p101_3 (m.d 0 4) (by simp) with h125 | h125
                                          · linarith only [h125, h6, hlam]
                                          · linarith only [h125, h69, hlam]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h69, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h95, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h99, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [h100, hlam, p101_0]
                                        · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                          linarith only [hlam, p101_0]
                                      · linarith only [h100, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h88, h95, h99, hlam]
                                  · linarith only [h70, h94, h98, hlam]
                              · linarith only [h95, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h6, h68, h94, hc13, hc34, hlam, hphi]
                  · linarith only [h69, hlam, hphi, ht45, u4ehi0, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                          · linarith only [h1, h139, h143, h6, h68, hlam, hphi, ht45, u4ehi4, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                            · linarith only [h1, h145, h68, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                                · linarith only [h1, h140, h147, h148, h2, h6, h68, hlam, hphi, ht45, u4ehi4, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h150 | h150
                                  · linarith only [h1, h140, h150, h68, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h152 | h152
                                    · linarith only [h0, h141, h152, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h152, hlam, hphi, ht45, u4ehi2, u5elo4]
                              · linarith only [h139, h147, h68, hlam, hphi, ht45, u4ehi1, u5elo3]
                        · linarith only [h140, h142, h5, h68, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                        · linarith only [h0, h141, h157, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                        · linarith only [h140, h157, h5, h68, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h140, h3, h68, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h139, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h4, h5, hlam, hphi, ht45, u4ehi2, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h163 | h163
            · rcases m.htr 0 3 4 (by decide) (by decide) with h164 | h164
              · linarith only [h164, h3, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
                · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                      · linarith only [h166, h169, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                          · linarith only [h164, h166, h172, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                                · linarith only [h1, h164, h174, h176, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                  · linarith only [h0, h168, h178, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                                  · linarith only [h1, h174, h176, h178, h3, h4, hc23, hc34, hlam, hphi]
                              · linarith only [h175, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h164, h166, h174, hc13, hc34, hlam, hphi]
                        · linarith only [h163, h171, h4, hc12, hc24, hlam, hphi]
                    · linarith only [h168, h3, h4, hc12, hc24, hlam, hphi]
                  · linarith only [h167, hlam, hphi, ht45, u4ehi0, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                      · linarith only [h163, h188, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                          · linarith only [h1, h166, h191, hlam, hphi, ht45, u4ehi3, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                            · linarith only [h1, h166, h193, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                                · linarith only [h164, h196, h3, h4, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                                  · linarith only [h1, h166, h187, h198, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                                      · rcases h4bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h188, h190, h200, hc04, hlam, hphi, ht0b, ht45, ht5b, p202_1, u4ehi4]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h4, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h164, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          rcases p202_3 (m.d 0 4) (by simp) with h207 | h207
                                          · rcases p202_3 (m.d 1 4) (by simp) with h208 | h208
                                            · linarith only [h2, h208, hlam]
                                            · linarith only [h195, h208, hlam]
                                          · linarith only [h207, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h2, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h188, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h191, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p202_1, u4ehi4]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h0, h190, h200, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p202_1, u4ehi4]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h188, h190, h196, h200, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p202_1, u4ehi4]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h196, hlam, p202_1]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          rcases p202_3 (m.d 0 4) (by simp) with h221 | h221
                                          · linarith only [h221, h4, hlam]
                                          · linarith only [h186, h221, hlam]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h0, h190, h200, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p202_1, u4ehi4]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h188, h190, h200, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p202_1, u4ehi4]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h0, h190, h200, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p202_1, u4ehi4]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          rcases p202_3 (m.d 0 4) (by simp) with h228 | h228
                                          · linarith only [h164, h228, hlam]
                                          · linarith only [h186, h228, hlam]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h186, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h195, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h200, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [h201, hlam, p202_0]
                                        · obtain ⟨p202_0, p202_1, p202_2, p202_3⟩ := h202c
                                          linarith only [hlam, p202_0]
                                      · linarith only [h0, h190, h200, h201, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                    · linarith only [h0, h190, h195, h200, h4, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                              · linarith only [h195, hlam, hphi, ht45, u4ehi1, u5elo4]
                        · linarith only [h163, h190, h4, hc12, hc24, hlam, hphi]
                    · linarith only [h187, h3, h4, hc12, hc24, hlam, hphi]
                  · linarith only [h163, h186, h4, hlam, hphi, u5ehi7, u5elo4]
            · linarith only [h163, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h243 | h243
          · rcases m.htr 0 2 5 (by decide) (by decide) with h244 | h244
            · rcases m.htr 0 3 4 (by decide) (by decide) with h245 | h245
              · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
                · rcases m.htr 0 4 5 (by decide) (by decide) with h247 | h247
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                    · linarith only [h243, h247, h248, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h253 | h253
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h254 | h254
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h255 | h255
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
                                    · linarith only [h243, h257, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                    · linarith only [h257, hlam, hphi, ht45, u4ehi2, u5elo4]
                                  · linarith only [h0, h251, h256, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                                · linarith only [h0, h251, h255, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                              · linarith only [h243, h247, h254, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                            · linarith only [h246, h248, h250, h253, hlam, hphi, ht45, u4ehi2, u5elo0]
                          · linarith only [h245, h248, h250, h252, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h250, h251, hlam, hphi, ht45, u4ehi2, u5elo2]
                      · linarith only [h243, h250, h3, hc12, hc23, hlam, hphi]
                  · linarith only [h247, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h244, h246, h3, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h243, h245, h3, hlam]
            · linarith only [h243, h244, hlam, hphi, ht45, u4ehi2, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h271 | h271
            · rcases m.htr 0 3 4 (by decide) (by decide) with h272 | h272
              · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
                · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                    · linarith only [h0, h275, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                      · linarith only [h0, h243, h277, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h280 | h280
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h281 | h281
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h282 | h282
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h286 | h286
                                      · linarith only [h1, h280, h286, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h0, h243, h279, h283, h285, h286, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                    · linarith only [h0, h243, h279, h285, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                                  · linarith only [h0, h279, h284, h3, hlam, hphi, u5ehi7, u5elo3]
                                · linarith only [h0, h279, h283, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                              · linarith only [h282, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h277, h279, h280, h281, hlam, hphi, u5ehi7, u5elo3]
                          · linarith only [h272, h275, h279, h280, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h271, h279, h3, hc12, hc23, hlam, hphi]
                  · linarith only [h274, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h272, h273, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
                · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
                    · linarith only [h271, h3, h300, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
                      · linarith only [h0, h243, h302, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                          · linarith only [h272, h298, h305, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                                · linarith only [h0, h272, h3, h304, h309, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                                · linarith only [h0, h3, h304, h309, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                              · linarith only [h300, h304, h305, h308, hlam, hphi, u5ehi7, u5elo4]
                            · linarith only [h300, h304, h307, hlam, hphi, u5ehi7, u5elo3]
                        · linarith only [h271, h3, h304, hc12, hc23, hlam, hphi]
                  · linarith only [h299, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h271, h298, h3, hlam, hphi, u5ehi7, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 3 5 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 4 5 (by decide) (by decide) with h319 | h319
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                    · linarith only [h0, h3, h317, h319, h320, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
                      · linarith only [h0, h243, h271, h319, h322, hlam, hphi, ht45, u4ehi4, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                        · linarith only [h0, h271, h324, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h326 | h326
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h327 | h327
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h328 | h328
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                                      · linarith only [h1, h326, h332, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h332, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h243, h271, h319, h331, hlam, hphi, ht45, u4ehi0, u5elo2]
                                  · linarith only [h1, h3, h327, h330, hlam]
                                · linarith only [h3, h317, h329, hlam]
                              · linarith only [h328, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h326, h327, hlam, hphi, ht45, u4ehi3, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
                            · linarith only [h3, h317, h326, h340, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h342 | h342
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h343 | h343
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h344 | h344
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h346 | h346
                                      · rcases h4bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h271, h3, h317, h318, h320, h340, h342, hc12, hc23, hlam, hphi, ht45, p347_1, u4ehi4, u5elo2]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h243, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h3, h317, h320, h326, hc12, hc23, hlam, hphi, p347_1]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          rcases p347_3 (m.d 0 4) (by simp) with h352 | h352
                                          · rcases p347_3 (m.d 1 4) (by simp) with h353 | h353
                                            · linarith only [h2, h353, hlam]
                                            · linarith only [h342, h353, hlam]
                                          · linarith only [h352, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h2, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h322, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h326, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi4]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h271, h318, h319, h320, h340, h343, hc12, hc23, hlam, hphi, ht45, p347_1, u4ehi4, u5elo2]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h271, h318, h320, h340, h342, h343, hc12, hc23, hlam, hphi, ht45, p347_1, u4ehi4, u5elo2]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h271, h318, h320, h326, h340, h342, h343, hc12, hc23, hlam, hphi, ht45, p347_1, u4ehi4, u5elo2]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          rcases p347_3 (m.d 0 4) (by simp) with h366 | h366
                                          · linarith only [h243, h366, hlam]
                                          · linarith only [h319, h366, hlam]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h317, hlam, p347_1]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h317, h342, hc04, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi4]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h343, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h271, h3, h317, h318, h320, h340, hc12, hc23, hlam, hphi, ht45, p347_1, u4ehi4, u5elo2]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h319, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h342, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h345, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [h346, hlam, p347_0]
                                        · obtain ⟨p347_0, p347_1, p347_2, p347_3⟩ := h347c
                                          linarith only [hlam, p347_0]
                                      · linarith only [h346, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h243, h271, h3, h317, h318, h320, h326, h340, h342, h345, hc12, hc23, hlam, hphi, ht45, u4ehi0, u5elo2]
                                  · linarith only [h271, h3, h317, h318, h326, h344, hlam, hphi, ht45, u4ehi1, u5elo2]
                                · linarith only [h3, h317, h343, hlam]
                              · linarith only [h342, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h319, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h317, h318, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h386 | h386
                · rcases m.htr 0 4 5 (by decide) (by decide) with h387 | h387
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
                    · linarith only [h0, h3, h386, h388, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                      · linarith only [h0, h243, h271, h317, h386, h390, hlam, hphi, u5ehi8, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
                        · linarith only [h0, h271, h392, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
                          · linarith only [h317, h386, h394, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h396 | h396
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h397 | h397
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h398 | h398
                                · linarith only [h1, h317, h396, h398, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h400 | h400
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
                                      · rcases h4bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h394, h396, h402, hc04, hlam, hphi, ht0b, ht45, ht5b, p403_1, u4ehi4]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h243, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h317, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          rcases p403_3 (m.d 0 4) (by simp) with h408 | h408
                                          · rcases p403_3 (m.d 1 4) (by simp) with h409 | h409
                                            · linarith only [h2, h409, hlam]
                                            · linarith only [h397, h409, hlam]
                                          · linarith only [h408, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h2, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h390, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h394, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p403_1, u4ehi4]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h1, h317, h396, h398, h402, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p403_1, u4ehi4]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h394, h396, h398, h402, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p403_1, u4ehi4]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h398, hlam, p403_1]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          rcases p403_3 (m.d 0 4) (by simp) with h422 | h422
                                          · linarith only [h243, h422, hlam]
                                          · linarith only [h387, h422, hlam]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h1, h317, h396, h402, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p403_1, u4ehi4]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h394, h396, h402, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p403_1, u4ehi4]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h243, hc02, hc34, hlam, hphi, ht23, p403_1]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          rcases p403_3 (m.d 0 4) (by simp) with h429 | h429
                                          · linarith only [h317, h429, hlam]
                                          · linarith only [h387, h429, hlam]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h387, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h397, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h401, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [h402, hlam, p403_0]
                                        · obtain ⟨p403_0, p403_1, p403_2, p403_3⟩ := h403c
                                          linarith only [hlam, p403_0]
                                      · linarith only [h402, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h1, h243, h317, h396, h397, h401, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                                  · linarith only [h0, h1, h243, h3, h317, h396, h400, hc12, hc24, hlam, hphi]
                              · linarith only [h271, h387, h397, hlam, hphi, ht45, u4ehi1, u5elo2]
                            · linarith only [h317, h386, h396, hc13, hc34, hlam, hphi]
                  · linarith only [h387, hlam, hphi, ht45, u4ehi0, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                    · linarith only [h0, h3, h444, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                      · linarith only [h0, h243, h3, h443, h446, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h448 | h448
                        · linarith only [h1, h271, h386, h444, h448, hlam, hphi, u5ehi5, u5elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                          · linarith only [h1, h386, h450, hlam, hphi, ht45, u4ehi3, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                            · linarith only [h1, h386, h452, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h454 | h454
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h458 | h458
                                      · rcases h4bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h454, hc04, hlam, hphi, ht0b, ht45, ht5b, p459_1, u4ehi4]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h243, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h317, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h1, h317, h386, h444, h455, h456, hc12, hc23, hlam, hphi, ht45, p459_1, u4ehi4, u5elo2]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h2, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h446, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h450, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p459_1, u4ehi4]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h1, h386, h443, h444, h456, hc12, hc24, hlam, hphi, ht45, p459_1, u4ehi4, u5elo2]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h1, h386, h444, h454, h456, hc12, hc24, hlam, hphi, ht45, p459_1, u4ehi4, u5elo2]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h1, h317, h444, h455, hc12, hc23, hlam, hphi, p459_1]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          rcases p459_3 (m.d 0 4) (by simp) with h474 | h474
                                          · linarith only [h243, h474, hlam]
                                          · linarith only [h443, h474, hlam]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h1, h2, h386, h444, h454, h456, hc12, hc34, hlam, hphi, ht23, ht45, p459_1, u4ehi4, u5elo2]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h1, h386, h444, h454, h456, hc12, hc34, hlam, hphi, ht23, ht45, p459_1, u4ehi4, u5elo2]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h455, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h1, h386, h444, h455, h456, hc12, hc23, hlam, hphi, ht45, p459_1, u4ehi4, u5elo2]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h443, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h454, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h457, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [h458, hlam, p459_0]
                                        · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                                          linarith only [hlam, p459_0]
                                      · linarith only [h443, h458, hlam, hphi, ht45, u4ehi3, u5elo0]
                                    · linarith only [h1, h2, h317, h386, h444, h454, h455, h456, h457, hc12, hc23, hlam, hphi, ht45, u4ehi2, u5elo2]
                                  · linarith only [h2, h317, h454, h455, h456, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h490 | h490
                                  · linarith only [h1, h386, h444, h455, h490, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h3, h490, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h454, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h2, h443, hlam, hphi, ht45, u4ehi1, u5elo4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h495 | h495
        · rcases m.htr 0 2 4 (by decide) (by decide) with h496 | h496
          · linarith only [h0, h2, h496, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h498 | h498
            · rcases m.htr 0 3 4 (by decide) (by decide) with h499 | h499
              · linarith only [h1, h2, h499, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h501 | h501
                · rcases m.htr 0 4 5 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                      · linarith only [h496, h498, h504, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                        · linarith only [h0, h2, h504, h506, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h503, h506, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h495, h496, h503, hc12, hc24, hlam, hphi]
                  · linarith only [h502, hlam, hphi, ht45, u4ehi0, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h511 | h511
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h513 | h513
                      · linarith only [h0, h496, h498, h513, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                        · linarith only [h0, h2, h513, h515, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h0, h2, h498, h513, h515, hc12, hc24, hlam, hphi]
                    · linarith only [h495, h501, h512, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h511, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h495, h498, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h521 | h521
          · linarith only [h1, h2, h495, h521, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h523 | h523
            · rcases m.htr 0 3 4 (by decide) (by decide) with h524 | h524
              · linarith only [h1, h2, h524, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h526 | h526
                · rcases m.htr 0 4 5 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
                    · linarith only [h495, h523, h528, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h530 | h530
                      · linarith only [h1, h521, h523, h528, h530, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h532 | h532
                        · linarith only [h1, h2, h528, h530, h532, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h495, h523, h532, hc12, hc23, hlam, hphi]
                  · linarith only [h527, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h495, h523, h526, hlam, hphi, u5ehi7, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h537 | h537
              · linarith only [h1, h2, h537, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h539 | h539
                · rcases m.htr 0 4 5 (by decide) (by decide) with h540 | h540
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
                    · linarith only [h0, h495, h541, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h543 | h543
                      · linarith only [h0, h523, h543, hlam, hphi, ht45, u4ehi2, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h545 | h545
                        · linarith only [h0, h523, h545, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h547 | h547
                          · linarith only [h1, h2, h537, h543, h547, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
                            · linarith only [h1, h2, h547, h549, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                            · linarith only [h1, h2, h539, h547, h549, hc13, hc34, hlam, hphi]
                  · linarith only [h540, hlam, hphi, ht45, u4ehi0, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h553 | h553
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h554 | h554
                    · linarith only [h0, h495, h554, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h556 | h556
                      · linarith only [h1, h2, h554, h556, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h558 | h558
                        · linarith only [h1, h539, h554, h558, hlam, hphi, u5ehi7, u5elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                          · linarith only [h1, h539, h560, hlam, hphi, ht45, u4ehi3, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h562 | h562
                            · linarith only [h1, h539, h562, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h564 | h564
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h565 | h565
                                · linarith only [h1, h2, h554, h560, h565, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h567 | h567
                                  · linarith only [h539, h565, h567, hc03, hc34, hlam, hphi]
                                  · linarith only [h0, h495, h567, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h1, h2, h553, h554, h564, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h553, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h572 | h572
      · rcases m.htr 0 2 3 (by decide) (by decide) with h573 | h573
        · linarith only [h0, h1, h573, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h575 | h575
          · rcases m.htr 0 2 5 (by decide) (by decide) with h576 | h576
            · rcases m.htr 0 3 4 (by decide) (by decide) with h577 | h577
              · rcases m.htr 0 3 5 (by decide) (by decide) with h578 | h578
                · rcases m.htr 0 4 5 (by decide) (by decide) with h579 | h579
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
                    · linarith only [h573, h575, h579, h580, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h582 | h582
                      · linarith only [h0, h1, h580, h582, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h1, h575, h580, h582, hc12, hc23, hlam, hphi]
                  · linarith only [h579, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h0, h1, h575, h578, hlam, hphi, ht45, u4ehi2, u5elo3]
              · linarith only [h1, h572, h577, hlam]
            · linarith only [h575, h576, hlam, hphi, ht45, u4ehi2, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h589 | h589
            · rcases m.htr 0 3 4 (by decide) (by decide) with h590 | h590
              · rcases m.htr 0 3 5 (by decide) (by decide) with h591 | h591
                · rcases m.htr 0 4 5 (by decide) (by decide) with h592 | h592
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h593 | h593
                    · linarith only [h573, h589, h593, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h595 | h595
                      · linarith only [h0, h575, h589, h595, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h597 | h597
                        · linarith only [h1, h572, h593, h595, h597, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h575, h589, h597, hc12, hc24, hlam, hphi]
                  · linarith only [h592, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h1, h572, h575, h589, h591, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h1, h572, h590, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h603 | h603
              · rcases m.htr 0 3 5 (by decide) (by decide) with h604 | h604
                · rcases m.htr 0 4 5 (by decide) (by decide) with h605 | h605
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                    · linarith only [h0, h589, h606, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h608 | h608
                      · linarith only [h0, h575, h589, h605, h608, hlam, hphi, ht45, u4ehi4, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h610 | h610
                        · linarith only [h0, h589, h610, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h612 | h612
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h613 | h613
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h614 | h614
                              · linarith only [h1, h572, h606, h614, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · linarith only [h614, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h1, h572, h605, h613, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                          · linarith only [h1, h572, h605, h612, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                  · linarith only [h605, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h1, h572, h604, hlam, hphi, ht45, u4ehi1, u5elo3]
              · linarith only [h1, h572, h603, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h622 | h622
        · linarith only [h0, h1, h622, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h624 | h624
          · linarith only [h0, h572, h624, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h626 | h626
            · rcases m.htr 0 3 4 (by decide) (by decide) with h627 | h627
              · rcases m.htr 0 3 5 (by decide) (by decide) with h628 | h628
                · rcases m.htr 0 4 5 (by decide) (by decide) with h629 | h629
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                    · linarith only [h0, h1, h622, h630, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h632 | h632
                      · linarith only [h0, h1, h624, h626, h630, h632, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h634 | h634
                        · linarith only [h0, h1, h630, h634, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h0, h1, h626, h630, h634, hc12, hc23, hlam, hphi]
                  · linarith only [h629, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h0, h572, h626, h627, h628, hlam, hphi, u5ehi7, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h639 | h639
                · rcases m.htr 0 4 5 (by decide) (by decide) with h640 | h640
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h641 | h641
                    · linarith only [h0, h1, h627, h641, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h643 | h643
                      · linarith only [h0, h1, h627, h643, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h645 | h645
                        · linarith only [h0, h1, h627, h645, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h0, h1, h626, h627, h645, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h640, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h0, h1, h626, h639, hlam, hphi, u5ehi7, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h650 | h650
              · rcases m.htr 0 3 5 (by decide) (by decide) with h651 | h651
                · rcases m.htr 0 4 5 (by decide) (by decide) with h652 | h652
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
                    · linarith only [h0, h1, h622, h650, h652, h653, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h655 | h655
                      · linarith only [h0, h624, h652, h655, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
                        · linarith only [h0, h626, h657, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h659 | h659
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h660 | h660
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h663 | h663
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h664 | h664
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h665 | h665
                                      · rcases h4bigk with h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h572, hlam, p666_1]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h624, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h665, hc04, hlam, hphi, ht0b, ht45, ht5b, p666_1, u4ehi4]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          rcases p666_3 (m.d 0 4) (by simp) with h671 | h671
                                          · rcases p666_3 (m.d 1 4) (by simp) with h672 | h672
                                            · rcases p666_3 (m.d 2 4) (by simp) with h673 | h673
                                              · rcases p666_3 (m.d 3 4) (by simp) with h674 | h674
                                                · linarith only [h650, h674, hlam]
                                                · linarith only [h665, h674, hlam]
                                              · linarith only [h664, h673, hlam]
                                            · linarith only [h661, h672, hlam]
                                          · linarith only [h671, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h0, h572, h653, h659, hc12, hc23, hlam, hphi, p666_1]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h655, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h653, h659, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p666_1, u4ehi4]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          rcases p666_3 (m.d 0 4) (by simp) with h684 | h684
                                          · linarith only [h572, h684, hlam]
                                          · linarith only [h652, h684, hlam]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h650, h662, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p666_1, u4ehi4]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h0, h572, h662, hc12, hc23, hlam, hphi, p666_1]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h662, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p666_1, u4ehi4]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          rcases p666_3 (m.d 0 4) (by simp) with h691 | h691
                                          · linarith only [h624, h691, hlam]
                                          · linarith only [h652, h691, hlam]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h650, hlam, p666_1]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h659, hlam, p666_1]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h662, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h650, hc03, hlam, hphi, ht0b, ht45, ht5b, p666_1, u4ehi4]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h652, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h661, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h664, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [h665, hlam, p666_0]
                                        · obtain ⟨p666_0, p666_1, p666_2, p666_3⟩ := h666c
                                          linarith only [hlam, p666_0]
                                      · linarith only [h665, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h626, h652, h664, hlam, hphi, ht45, u4ehi2, u5elo2]
                                  · linarith only [h0, h1, h653, h663, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h0, h1, h653, h662, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h572, h650, h652, h661, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h650, h660, hlam, hphi, ht45, u4ehi3, u5elo3]
                          · linarith only [h0, h1, h659, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h652, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h0, h1, h651, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h713 | h713
                · rcases m.htr 0 4 5 (by decide) (by decide) with h714 | h714
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h715 | h715
                    · linarith only [h0, h1, h650, h715, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h717 | h717
                      · linarith only [h0, h626, h717, hlam, hphi, ht45, u4ehi2, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
                        · linarith only [h0, h626, h719, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h721 | h721
                          · linarith only [h0, h1, h650, h715, h721, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h721, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h714, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h0, h1, h713, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h726 | h726
    · rcases m.htr 0 1 4 (by decide) (by decide) with h727 | h727
      · rcases m.htr 0 2 3 (by decide) (by decide) with h728 | h728
        · rcases m.htr 0 2 4 (by decide) (by decide) with h729 | h729
          · rcases m.htr 0 2 5 (by decide) (by decide) with h730 | h730
            · rcases m.htr 0 3 4 (by decide) (by decide) with h731 | h731
              · rcases m.htr 0 3 5 (by decide) (by decide) with h732 | h732
                · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                          · linarith only [h0, h726, h737, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h739 | h739
                            · linarith only [h0, h726, h731, h737, h739, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h741 | h741
                              · linarith only [h0, h726, h731, h737, h741, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h735, h741, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h0, h726, h731, h736, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h726, h731, h733, h735, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h726, h731, h733, h734, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h733, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h731, h732, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h749 | h749
                · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h754 | h754
                          · linarith only [h731, h749, h754, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h756 | h756
                            · linarith only [h0, h727, h754, h756, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                            · linarith only [h731, h749, h756, hc13, hc34, hlam, hphi]
                        · linarith only [h0, h727, h753, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h727, h750, h752, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h727, h750, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h750, hlam, hphi, ht45, u4ehi0, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h763 | h763
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h764 | h764
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h765 | h765
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h766 | h766
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
                          · linarith only [h726, h731, h763, h767, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h769 | h769
                            · linarith only [h0, h726, h749, h769, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi5]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h771 | h771
                              · linarith only [h0, h727, h771, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h763, h771, hlam, hphi, ht45, u4ehi1, u5elo0]
                        · linarith only [h0, h727, h763, h766, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                      · linarith only [h0, h727, h763, h765, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h727, h763, h764, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h763, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h0, h727, h730, hlam, hphi, ht45, u4ehi1, u5elo2]
          · linarith only [h0, h727, h729, hlam]
        · linarith only [h0, h726, h728, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h781 | h781
        · rcases m.htr 0 2 4 (by decide) (by decide) with h782 | h782
          · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
            · rcases m.htr 0 3 4 (by decide) (by decide) with h784 | h784
              · linarith only [h726, h727, h784, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
                · rcases m.htr 0 4 5 (by decide) (by decide) with h787 | h787
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h790 | h790
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
                          · linarith only [h726, h727, h784, h789, h791, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h793 | h793
                            · linarith only [h726, h727, h791, h793, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                            · linarith only [h726, h727, h786, h788, h791, h793, hc23, hc34, hlam, hphi]
                        · linarith only [h726, h727, h783, h786, h789, h790, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h0, h726, h786, h789, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · linarith only [h0, h726, h786, h788, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · linarith only [h787, hlam, hphi, ht45, u4ehi0, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h800 | h800
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h801 | h801
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h803 | h803
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h804 | h804
                          · linarith only [h0, h726, h804, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h806 | h806
                            · linarith only [h726, h786, h806, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h808 | h808
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h809 | h809
                                · linarith only [h0, h726, h727, h781, h804, h809, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h811 | h811
                                  · linarith only [h726, h727, h786, h801, h811, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h813 | h813
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h814 | h814
                                      · rcases h4bigk with h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h727, hlam, p815_1]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h813, hc04, hlam, hphi, ht0b, ht45, ht5b, p815_1, u4ehi4]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h784, hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          rcases p815_3 (m.d 0 4) (by simp) with h820 | h820
                                          · rcases p815_3 (m.d 1 4) (by simp) with h821 | h821
                                            · rcases p815_3 (m.d 2 4) (by simp) with h822 | h822
                                              · linarith only [h782, h822, hlam]
                                              · linarith only [h813, h822, hlam]
                                            · linarith only [h808, h821, hlam]
                                          · linarith only [h820, hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h726, h727, h801, h804, hc23, hc34, hlam, hphi, p815_1]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h804, h813, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p815_1, u4ehi4]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h804, hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          rcases p815_3 (m.d 0 4) (by simp) with h831 | h831
                                          · linarith only [h727, h831, hlam]
                                          · linarith only [h800, h831, hlam]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h782, hlam, p815_1]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h802, hlam, p815_1]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h809, hlam, p815_1]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h0, h782, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p815_1, u4ehi4]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h726, h727, h801, hc23, hc34, hlam, hphi, p815_1]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h726, h727, h801, hc23, hc34, hlam, hphi, p815_1]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h813, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p815_1, u4ehi4]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          rcases p815_3 (m.d 0 4) (by simp) with h843 | h843
                                          · linarith only [h784, h843, hlam]
                                          · linarith only [h800, h843, hlam]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h800, hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h808, hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h813, hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [h814, hlam, p815_0]
                                        · obtain ⟨p815_0, p815_1, p815_2, p815_3⟩ := h815c
                                          linarith only [hlam, p815_0]
                                      · linarith only [h814, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h813, hlam, hphi, ht45, u4ehi2, u5elo4]
                              · linarith only [h727, h800, h808, hlam]
                        · linarith only [h0, h726, h783, h786, h801, h803, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h782, h802, hlam]
                    · linarith only [h0, h726, h781, h801, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h800, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h0, h726, h783, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h859 | h859
            · rcases m.htr 0 3 4 (by decide) (by decide) with h860 | h860
              · linarith only [h0, h726, h782, h860, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h862 | h862
                · rcases m.htr 0 4 5 (by decide) (by decide) with h863 | h863
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h864 | h864
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h865 | h865
                      · linarith only [h0, h726, h782, h862, h865, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · linarith only [h0, h726, h862, h865, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · linarith only [h0, h726, h862, h864, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · linarith only [h0, h726, h782, h862, h863, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h872 | h872
                      · linarith only [h782, h859, h872, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h874 | h874
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h875 | h875
                          · linarith only [h0, h726, h872, h875, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h877 | h877
                            · linarith only [h0, h726, h862, h872, h877, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h879 | h879
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h880 | h880
                                · linarith only [h0, h726, h871, h872, h875, h880, hlam]
                                · linarith only [h0, h726, h871, h872, h880, hc23, hc34, hlam, hphi]
                              · linarith only [h879, hlam, hphi, ht45, u4ehi1, u5elo4]
                        · linarith only [h0, h726, h859, h871, h874, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h781, h871, hlam]
                  · linarith only [h870, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h0, h726, h859, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h0, h726, h781, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h889 | h889
      · rcases m.htr 0 2 3 (by decide) (by decide) with h890 | h890
        · rcases m.htr 0 2 4 (by decide) (by decide) with h891 | h891
          · rcases m.htr 0 2 5 (by decide) (by decide) with h892 | h892
            · rcases m.htr 0 3 4 (by decide) (by decide) with h893 | h893
              · rcases m.htr 0 3 5 (by decide) (by decide) with h894 | h894
                · rcases m.htr 0 4 5 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h897 | h897
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h898 | h898
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h899 | h899
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h900 | h900
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h901 | h901
                              · linarith only [h726, h889, h896, h901, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h899, h901, hlam, hphi, ht45, u4ehi3, u5elo4]
                            · linarith only [h726, h889, h890, h894, h900, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h726, h889, h895, h899, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h890, h898, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h889, h895, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h889, h895, h896, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h895, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h726, h889, h894, hlam, hphi, ht45, u4ehi1, u5elo3]
              · linarith only [h726, h889, h893, hlam]
            · linarith only [h726, h889, h890, h892, hlam, hphi, ht45, u4ehi1, u5elo2]
          · linarith only [h726, h889, h890, h891, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h914 | h914
          · rcases m.htr 0 2 5 (by decide) (by decide) with h915 | h915
            · rcases m.htr 0 3 4 (by decide) (by decide) with h916 | h916
              · rcases m.htr 0 3 5 (by decide) (by decide) with h917 | h917
                · rcases m.htr 0 4 5 (by decide) (by decide) with h918 | h918
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h919 | h919
                    · linarith only [h0, h889, h890, h918, h919, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h889, h918, h919, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h918, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h0, h889, h890, h917, hlam, hphi, ht45, u4ehi1, u5elo3]
              · linarith only [h0, h889, h890, h916, hlam]
            · linarith only [h0, h889, h915, hlam, hphi, ht45, u4ehi1, u5elo2]
          · linarith only [h0, h889, h914, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h927 | h927
        · rcases m.htr 0 2 4 (by decide) (by decide) with h928 | h928
          · rcases m.htr 0 2 5 (by decide) (by decide) with h929 | h929
            · rcases m.htr 0 3 4 (by decide) (by decide) with h930 | h930
              · rcases m.htr 0 3 5 (by decide) (by decide) with h931 | h931
                · rcases m.htr 0 4 5 (by decide) (by decide) with h932 | h932
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h933 | h933
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h934 | h934
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h935 | h935
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h936 | h936
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h937 | h937
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h938 | h938
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h941 | h941
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h942 | h942
                                      · linarith only [h927, h939, h942, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h942, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h938, h941, hlam, hphi, ht45, u4ehi2, u5elo1]
                                  · linarith only [h931, h939, h940, hlam, hphi, ht45, u4ehi3, u5elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h947 | h947
                                  · linarith only [h726, h930, h933, h939, h947, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h949 | h949
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h950 | h950
                                      · rcases h4bigk with h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h889, hlam, p951_1]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h726, h930, h933, h949, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi4]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h726, h930, h933, h939, h949, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi4]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          rcases p951_3 (m.d 0 4) (by simp) with h956 | h956
                                          · rcases p951_3 (m.d 1 4) (by simp) with h957 | h957
                                            · rcases p951_3 (m.d 2 4) (by simp) with h958 | h958
                                              · linarith only [h928, h958, hlam]
                                              · linarith only [h949, h958, hlam]
                                            · linarith only [h938, h957, hlam]
                                          · linarith only [h956, hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h928, h933, h936, h949, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi4]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h933, h936, h949, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi4]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h933, h936, h939, h949, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi4]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          rcases p951_3 (m.d 0 4) (by simp) with h967 | h967
                                          · linarith only [h889, h967, hlam]
                                          · linarith only [h932, h967, hlam]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h928, hlam, p951_1]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h934, hlam, p951_1]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h939, hlam, p951_1]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h0, h928, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi4]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h930, hlam, p951_1]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h936, hlam, p951_1]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h726, h930, h933, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi2]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h726, h930, h933, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1, u4ehi4]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h932, hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h938, hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h949, hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [h950, hlam, p951_0]
                                        · obtain ⟨p951_0, p951_1, p951_2, p951_3⟩ := h951c
                                          linarith only [hlam, p951_0]
                                      · linarith only [h950, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h938, h949, hlam, hphi, ht45, u4ehi2, u5elo1]
                              · linarith only [h889, h932, h938, hlam, hphi, ht45, u4ehi0, u5elo0]
                            · linarith only [h726, h931, h937, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                          · linarith only [h726, h930, h936, hlam]
                        · linarith only [h0, h935, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h928, h934, hlam]
                    · linarith only [h0, h927, h933, hlam]
                  · linarith only [h932, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h930, h931, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h995 | h995
                · rcases m.htr 0 4 5 (by decide) (by decide) with h996 | h996
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h998 | h998
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h999 | h999
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1000 | h1000
                          · linarith only [h1000, h930, h995, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1002 | h1002
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1003 | h1003
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1004 | h1004
                                · linarith only [h1000, h1004, h726, h927, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1006 | h1006
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1007 | h1007
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1008 | h1008
                                      · rcases h4bigk with h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h889, hlam, p1009_1]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1004, h1006, h1008, hc04, hlam, hphi, ht0b, ht45, ht5b, p1009_1, u4ehi4]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h930, hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          rcases p1009_3 (m.d 0 4) (by simp) with h1014 | h1014
                                          · rcases p1009_3 (m.d 1 4) (by simp) with h1015 | h1015
                                            · rcases p1009_3 (m.d 2 4) (by simp) with h1016 | h1016
                                              · linarith only [h1016, h928, hlam]
                                              · linarith only [h1007, h1016, hlam]
                                            · linarith only [h1003, h1015, hlam]
                                          · linarith only [h1014, hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1000, h1004, h1006, h1008, h928, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1009_1, u4ehi4]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1000, h1004, h1006, h1008, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1009_1, u4ehi4]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1000, hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          rcases p1009_3 (m.d 0 4) (by simp) with h1025 | h1025
                                          · linarith only [h1025, h889, hlam]
                                          · linarith only [h1025, h996, hlam]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h928, hlam, p1009_1]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h998, hlam, p1009_1]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1004, hlam, p1009_1]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h0, h928, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1009_1, u4ehi4]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1006, h1008, h927, h930, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1009_1, u4ehi4]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h889, hc01, hc34, hlam, hphi, ht12, ht23, p1009_1]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1004, h1006, h1008, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1009_1, u4ehi4]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          rcases p1009_3 (m.d 0 4) (by simp) with h1037 | h1037
                                          · linarith only [h1037, h930, hlam]
                                          · linarith only [h1037, h996, hlam]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h996, hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1003, hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1007, hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [h1008, hlam, p1009_0]
                                        · obtain ⟨p1009_0, p1009_1, p1009_2, p1009_3⟩ := h1009c
                                          linarith only [hlam, p1009_0]
                                      · linarith only [h1000, h1008, hc13, hlam, hphi, ht34, ht45, u5elo4]
                                    · linarith only [h1004, h1006, h1007, h889, h996, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                                  · linarith only [h1006, h930, h995, hc23, hc34, hlam, hphi]
                              · linarith only [h1003, h889, h996, hlam, hphi, ht45, u4ehi0, u5elo0]
                            · linarith only [h1002, h726, h995, hlam]
                        · linarith only [h0, h929, h999, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                      · linarith only [h0, h928, h998, hlam]
                    · linarith only [h0, h927, h997, hlam]
                  · linarith only [h930, h995, h996, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1054 | h1054
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1055 | h1055
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1056 | h1056
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1057 | h1057
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1058 | h1058
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1059 | h1059
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1060 | h1060
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1061 | h1061
                                · linarith only [h1054, h1059, h1061, h927, h930, h995, hlam, hphi, ht45, u4ehi4, u5elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1063 | h1063
                                  · linarith only [h1063, h927, h995, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1065 | h1065
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1066 | h1066
                                      · rcases h4bigk with h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h889, hlam, p1067_1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1065, hc04, hlam, hphi, ht0b, ht45, ht5b, p1067_1, u4ehi4]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h930, hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1055, h1058, h1059, h726, h930, h995, hc01, hc12, hlam, hphi, ht45, p1067_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1055, h1058, h1059, h1065, h726, h928, h995, hc01, hc12, hlam, hphi, ht45, p1067_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1055, h1058, h1059, h1065, h726, h995, hc01, hc12, hlam, hphi, ht45, p1067_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1055, h1058, h726, h930, hc01, hc12, hlam, hphi, p1067_1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          rcases p1067_3 (m.d 0 4) (by simp) with h1077 | h1077
                                          · linarith only [h1077, h889, hlam]
                                          · linarith only [h1054, h1077, hlam]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h928, hlam, p1067_1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1056, hlam, p1067_1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1061, hlam, p1067_1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h0, h1059, h726, h928, h995, hc01, hc12, hlam, hphi, ht45, p1067_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1054, h1059, h726, h995, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p1067_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1058, hlam, p1067_1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1055, h1058, h1059, h726, h995, hc01, hc12, hlam, hphi, ht45, p1067_1, u4ehi2, u5elo1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1055, h1058, h1059, h726, h995, hc01, hc12, hlam, hphi, ht45, p1067_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1054, hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1060, hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1065, hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [h1066, hlam, p1067_0]
                                        · obtain ⟨p1067_0, p1067_1, p1067_2, p1067_3⟩ := h1067c
                                          linarith only [hlam, p1067_0]
                                      · linarith only [h1066, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h1054, h1055, h1058, h1059, h1065, h726, h930, h995, hc01, hc12, hlam, hphi, ht45, u4ehi2, u5elo1]
                              · linarith only [h1054, h1055, h1058, h1059, h1060, h726, h930, h995, hc01, hc12, hlam, hphi, ht45, u4ehi1, u5elo1]
                            · linarith only [h1054, h1058, h1059, h930, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1099 | h1099
                            · linarith only [h1058, h1099, h726, h995, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1099, h726, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h1057, h929, h995, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h1056, h928, hlam]
                    · linarith only [h0, h1055, h927, hlam]
                  · linarith only [h1054, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h928, h929, hlam, hphi, ht45, u4ehi2, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1107 | h1107
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1108 | h1108
              · linarith only [h1108, h927, h928, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1110 | h1110
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1111 | h1111
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1112 | h1112
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1113 | h1113
                      · linarith only [h1107, h1113, h928, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1115 | h1115
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1116 | h1116
                          · linarith only [h1108, h1110, h1112, h1113, h1116, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1118 | h1118
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1119 | h1119
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1120 | h1120
                                · linarith only [h0, h1113, h1116, h1120, h927, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1122 | h1122
                                  · linarith only [h0, h1113, h1120, h1122, h927, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                                  · linarith only [h0, h1110, h1113, h1120, h1122, h927, hc23, hc34, hlam, hphi]
                              · linarith only [h1119, h889, hlam, hphi, ht45, u4ehi0, u5elo4]
                            · linarith only [h1110, h1118, h726, hlam]
                        · linarith only [h0, h1110, h1115, h927, hlam, hphi, u5ehi8, u5elo2]
                    · linarith only [h0, h1112, h927, hlam]
                  · linarith only [h1110, h1111, h927, h928, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
                      · linarith only [h1107, h1132, h928, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1134 | h1134
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1135 | h1135
                          · linarith only [h1107, h1108, h1131, h1132, h1135, h928, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1137 | h1137
                            · linarith only [h1110, h1135, h1137, hc03, hc34, hlam, hphi]
                            · linarith only [h1137, h726, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h1134, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h1131, h927, hlam]
                  · linarith only [h1130, hlam, hphi, ht45, u4ehi0, u5elo4]
            · linarith only [h1107, h927, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1144 | h1144
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1145 | h1145
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1146 | h1146
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1147 | h1147
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1148 | h1148
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1149 | h1149
                    · linarith only [h1144, h1148, h1149, h927, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1151 | h1151
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1152 | h1152
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1153 | h1153
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1154 | h1154
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1155 | h1155
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1156 | h1156
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1157 | h1157
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1158 | h1158
                                    · linarith only [h0, h1144, h1149, h1158, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                    · linarith only [h1156, h1158, hlam, hphi, ht45, u4ehi3, u5elo4]
                                  · linarith only [h0, h1145, h1149, h1157, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                                · linarith only [h0, h1145, h1149, h1156, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                              · linarith only [h1148, h1155, h889, hlam]
                            · linarith only [h1154, h726, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h1146, h1153, h726, hlam]
                        · linarith only [h0, h1144, h1152, hlam, hphi, ht45, u4ehi0, u5elo2]
                      · linarith only [h0, h1144, h1151, hlam]
                  · linarith only [h1148, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h1144, h1147, h927, hlam, hphi, ht45, u4ehi2, u5elo3]
              · linarith only [h1144, h1146, h927, hlam]
            · linarith only [h1144, h1145, hlam, hphi, ht45, u4ehi2, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1172 | h1172
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1173 | h1173
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1174 | h1174
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1175 | h1175
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1176 | h1176
                    · linarith only [h1172, h1176, h927, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1178 | h1178
                      · linarith only [h1144, h1172, h1178, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1180 | h1180
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1181 | h1181
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1182 | h1182
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1183 | h1183
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1184 | h1184
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1185 | h1185
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1186 | h1186
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1187 | h1187
                                      · rcases h4bigk with h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h889, hlam, p1188_1]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1144, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1173, h1187, hc03, hlam, hphi, ht0b, ht45, ht5b, p1188_1, u4ehi4]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          rcases p1188_3 (m.d 0 4) (by simp) with h1193 | h1193
                                          · rcases p1188_3 (m.d 1 4) (by simp) with h1194 | h1194
                                            · rcases p1188_3 (m.d 2 4) (by simp) with h1195 | h1195
                                              · rcases p1188_3 (m.d 3 4) (by simp) with h1196 | h1196
                                                · linarith only [h1173, h1196, hlam]
                                                · linarith only [h1187, h1196, hlam]
                                              · linarith only [h1186, h1195, hlam]
                                            · linarith only [h1183, h1194, hlam]
                                          · linarith only [h1193, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1144, h1172, h1178, h1185, h1187, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1188_1, u4ehi4]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1178, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1176, h1181, h1187, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1188_1, u4ehi4]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          rcases p1188_3 (m.d 0 4) (by simp) with h1206 | h1206
                                          · linarith only [h1206, h889, hlam]
                                          · linarith only [h1175, h1206, hlam]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1144, h1172, h1184, h1185, h1187, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1188_1, u4ehi4]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1184, h889, hc01, hc23, hlam, hphi, ht12, p1188_1]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1184, h1187, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1188_1, u4ehi4]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          rcases p1188_3 (m.d 0 4) (by simp) with h1213 | h1213
                                          · linarith only [h1144, h1213, hlam]
                                          · linarith only [h1175, h1213, hlam]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1173, hlam, p1188_1]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1181, hlam, p1188_1]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1184, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1173, h1176, h726, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1188_1, u4ehi4]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1175, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1183, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1186, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [h1187, hlam, p1188_0]
                                        · obtain ⟨p1188_0, p1188_1, p1188_2, p1188_3⟩ := h1188c
                                          linarith only [hlam, p1188_0]
                                      · linarith only [h1187, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h1186, hlam, hphi, ht45, u4ehi2, u5elo4]
                                  · linarith only [h1176, h1185, h726, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                                · linarith only [h0, h1172, h1176, h1184, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                              · linarith only [h1175, h1183, h889, hlam]
                            · linarith only [h1173, h1174, h1182, h726, hlam, hphi, ht45, u4ehi0, u5elo0]
                          · linarith only [h1173, h1181, h726, hlam]
                        · linarith only [h0, h1172, h1180, hlam]
                  · linarith only [h1144, h1172, h1175, hlam, hphi, u5ehi7, u5elo4]
                · linarith only [h1144, h1172, h1173, h1174, hlam, hphi, u5ehi7, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1238 | h1238
                    · linarith only [h1172, h1238, h927, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1240 | h1240
                      · linarith only [h1144, h1172, h1240, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1242 | h1242
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1243 | h1243
                          · linarith only [h1173, h1236, h1243, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1245 | h1245
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1246 | h1246
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1247 | h1247
                                · linarith only [h0, h1238, h1243, h1247, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1172, h1247, h927, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                              · linarith only [h0, h1172, h1238, h1243, h1246, hlam, hphi, u5ehi7, u5elo4]
                            · linarith only [h0, h1172, h1238, h1245, hlam, hphi, u5ehi7, u5elo3]
                        · linarith only [h0, h1172, h1242, hlam]
                  · linarith only [h1172, h1173, h1237, h927, hlam, hphi, u5ehi7, u5elo4]
                · linarith only [h1172, h1236, h927, hlam, hphi, u5ehi7, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1255 | h1255
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1256 | h1256
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1257 | h1257
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1258 | h1258
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1259 | h1259
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1260 | h1260
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1261 | h1261
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1262 | h1262
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1263 | h1263
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1264 | h1264
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1265 | h1265
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1266 | h1266
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1267 | h1267
                                      · linarith only [h1255, h1258, h1267, h927, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h1267, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h1144, h1257, h1266, hlam]
                                  · linarith only [h1256, h1265, h927, hlam]
                                · linarith only [h1255, h1264, h927, hlam]
                              · linarith only [h1144, h1257, h1259, h1263, hlam]
                            · linarith only [h1256, h1258, h1262, h927, hlam]
                          · linarith only [h1255, h1258, h1261, h927, hlam]
                        · linarith only [h0, h1260, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1255, h1258, h1259, h927, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1278 | h1278
                      · linarith only [h0, h1144, h1258, h1278, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1280 | h1280
                        · linarith only [h0, h1172, h1258, h1280, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1280, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1257, hlam, hphi, ht45, u4ehi0, u5elo4]
                · linarith only [h1255, h1256, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1285 | h1285
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1286 | h1286
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1287 | h1287
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1288 | h1288
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1289 | h1289
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1290 | h1290
                          · linarith only [h1255, h1285, h1290, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1292 | h1292
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1293 | h1293
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1294 | h1294
                                · linarith only [h1287, h1290, h1294, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1296 | h1296
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1297 | h1297
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1298 | h1298
                                      · rcases h4bigk with h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h889, hlam, p1299_1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1144, hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1255, hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h0, h1144, h1172, h1288, h1289, hc01, hc12, hlam, hphi, ht45, p1299_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h0, h1172, h1255, h1285, h1289, h1290, h1298, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p1299_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h0, h1144, h1172, h1255, h1285, h1289, h1290, h1298, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p1299_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1290, hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          rcases p1299_3 (m.d 0 4) (by simp) with h1309 | h1309
                                          · linarith only [h1309, h889, hlam]
                                          · linarith only [h1286, h1309, hlam]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h0, h1172, h1255, h1285, h1289, h1298, hc01, hc24, hlam, hphi, ht12, ht45, p1299_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1288, hlam, p1299_1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1294, hlam, p1299_1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h0, h1172, h1288, h1289, hc01, hc12, hlam, hphi, ht45, p1299_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h0, h1172, h1255, h1285, h1289, h1298, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p1299_1, u4ehi4, u5elo1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h889, hc01, hc34, hlam, hphi, ht12, ht23, p1299_1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h0, h1144, hc01, hc34, hlam, hphi, ht12, ht23, p1299_1]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          rcases p1299_3 (m.d 0 4) (by simp) with h1321 | h1321
                                          · linarith only [h1255, h1321, hlam]
                                          · linarith only [h1286, h1321, hlam]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1286, hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1293, hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1297, hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [h1298, hlam, p1299_0]
                                        · obtain ⟨p1299_0, p1299_1, p1299_2, p1299_3⟩ := h1299c
                                          linarith only [hlam, p1299_0]
                                      · linarith only [h1298, hlam, hphi, ht45, u4ehi3, u5elo4]
                                    · linarith only [h1144, h1286, h1297, hlam]
                                  · linarith only [h1285, h1296, h927, hlam]
                              · linarith only [h1144, h1286, h1288, h1293, hlam]
                            · linarith only [h1285, h1287, h1292, h927, hlam]
                        · linarith only [h0, h1289, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1285, h1287, h1288, h927, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1336 | h1336
                      · linarith only [h1144, h1287, h1336, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1338 | h1338
                        · linarith only [h0, h1172, h1287, h1338, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1338, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1255, h1285, h1286, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1342 | h1342
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1343 | h1343
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1344 | h1344
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1345 | h1345
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1346 | h1346
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1347 | h1347
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1348 | h1348
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1349 | h1349
                                · linarith only [h1255, h1342, h1343, h1349, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h0, h1346, h1349, h927, hc01, hc13, hlam, hphi]
                              · linarith only [h1144, h1342, h1344, h1348, hlam]
                            · linarith only [h1347, h726, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1354 | h1354
                            · linarith only [h1285, h1346, h1354, h927, hc02, hc34, hlam, hphi, ht23]
                            · linarith only [h1354, h726, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h1345, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1343, h1344, h927, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1359 | h1359
                      · linarith only [h0, h1144, h1343, h1359, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1361 | h1361
                        · linarith only [h0, h1172, h1343, h1361, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1361, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1342, hlam, hphi, ht45, u4ehi0, u5elo4]

set_option maxHeartbeats 3934000 in
theorem n7l_sAB0_M_LI_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
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
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                                        · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                        · linarith only [h19, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h15, h18, h3, hc24, hlam, hphi, ht45, u5elo0]
                                    · linarith only [h17, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                                    · linarith only [h0, h10, h13, h16, h24, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h24, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h15, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h14, hc13, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                                  · linarith only [h0, h13, h29, h31, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                                        · rcases h0bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h33, h35, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h10, h13, h33, h35, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h10, h13, h33, h35, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            rcases p36_3 (m.d 0 1) (by simp) with h41 | h41
                                            · rcases p36_3 (m.d 0 2) (by simp) with h42 | h42
                                              · linarith only [h0, h42, hlam]
                                              · linarith only [h42, h6, hlam]
                                            · linarith only [h3, h41, hlam]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h0, hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h10, h13, h33, h35, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h0, h10, h13, h33, h35, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            rcases p36_3 (m.d 0 1) (by simp) with h50 | h50
                                            · rcases p36_3 (m.d 0 2) (by simp) with h51 | h51
                                              · rcases p36_3 (m.d 0 3) (by simp) with h52 | h52
                                                · linarith only [h4, h52, hlam]
                                                · linarith only [h52, h8, hlam]
                                              · linarith only [h51, h6, hlam]
                                            · linarith only [h3, h50, hlam]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h1, hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h4, hlam, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h10, h13, h33, h35, h7, hc03, hc45, hlam, hphi, ht0b, ht5b, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            rcases p36_3 (m.d 0 1) (by simp) with h61 | h61
                                            · rcases p36_3 (m.d 0 2) (by simp) with h62 | h62
                                              · rcases p36_3 (m.d 0 3) (by simp) with h63 | h63
                                                · rcases p36_3 (m.d 0 4) (by simp) with h64 | h64
                                                  · linarith only [h64, h7, hlam]
                                                  · linarith only [h64, h9, hlam]
                                                · linarith only [h63, h8, hlam]
                                              · linarith only [h6, h62, hlam]
                                            · linarith only [h3, h61, hlam]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h2, hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h5, hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h7, hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            rcases p36_3 (m.d 0 1) (by simp) with h74 | h74
                                            · rcases p36_3 (m.d 0 2) (by simp) with h75 | h75
                                              · rcases p36_3 (m.d 0 3) (by simp) with h76 | h76
                                                · rcases p36_3 (m.d 0 4) (by simp) with h77 | h77
                                                  · rcases p36_3 (m.d 0 5) (by simp) with h78 | h78
                                                    · linarith only [h78, h9, hlam]
                                                    · rcases h0emin with h80 | h80 | h80 | h80 | h80
                                                      · rcases h4bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h10, h13, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p81_1, u4elo0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h31, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p81_1, u4elo0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h10, h13, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p81_1, u4elo0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          rcases p81_3 (m.d 0 4) (by simp) with h86 | h86
                                                          · rcases p81_3 (m.d 1 4) (by simp) with h87 | h87
                                                            · linarith only [h2, h87, hlam]
                                                            · linarith only [h30, h87, hlam]
                                                          · linarith only [h86, hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h2, hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h31, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p81_1, u4elo1]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h13, hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          rcases p81_3 (m.d 0 4) (by simp) with h95 | h95
                                                          · rcases p81_3 (m.d 1 4) (by simp) with h96 | h96
                                                            · rcases p81_3 (m.d 2 4) (by simp) with h97 | h97
                                                              · linarith only [h11, h97, hlam]
                                                              · linarith only [h34, h97, hlam]
                                                            · linarith only [h96, hlam, p81_0]
                                                          · linarith only [h9, h95, hlam]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h5, hlam, p81_1]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h11, hlam, p81_1]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h31, hlam, p81_1]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h0, h11, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h7, hlam, p81_1]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [hc14, hlam, hphi, p81_1, u4elo3]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h7, hc24, hlam, hphi, p81_1, u4elo0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          rcases p81_3 (m.d 0 4) (by simp) with h111 | h111
                                                          · rcases p81_3 (m.d 1 4) (by simp) with h112 | h112
                                                            · linarith only [h112, h13, hlam]
                                                            · linarith only [h112, h30, hlam]
                                                          · linarith only [h111, h9, hlam]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h9, hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h30, hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h34, hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [h35, hlam, p81_0]
                                                        · obtain ⟨p81_0, p81_1, p81_2, p81_3⟩ := h81c
                                                          linarith only [hlam, p81_0]
                                                      · rcases h4bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h10, h13, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p121_1, u4elo0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h31, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p121_1, u4elo0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [hc34, hlam, hphi, p121_1, u4elo0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          rcases p121_3 (m.d 0 4) (by simp) with h126 | h126
                                                          · rcases p121_3 (m.d 1 4) (by simp) with h127 | h127
                                                            · linarith only [h127, h2, hlam]
                                                            · linarith only [h127, h30, hlam]
                                                          · linarith only [h126, hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h2, hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h31, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p121_1, u4elo1]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h13, hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          rcases p121_3 (m.d 0 4) (by simp) with h135 | h135
                                                          · rcases p121_3 (m.d 1 4) (by simp) with h136 | h136
                                                            · rcases p121_3 (m.d 2 4) (by simp) with h137 | h137
                                                              · linarith only [h11, h137, hlam]
                                                              · linarith only [h137, h34, hlam]
                                                            · linarith only [h136, hlam, p121_0]
                                                          · linarith only [h135, h9, hlam]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h5, hlam, p121_1]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h11, hlam, p121_1]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h31, hlam, p121_1]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h0, h11, hc01, hc45, hlam, hphi, ht0b, ht5b, p121_1]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h7, hlam, p121_1]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h7, hc14, hlam, hphi, p121_1, u4elo0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h7, hc24, hlam, hphi, p121_1, u4elo0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          rcases p121_3 (m.d 0 4) (by simp) with h151 | h151
                                                          · rcases p121_3 (m.d 1 4) (by simp) with h152 | h152
                                                            · linarith only [h13, h152, hlam]
                                                            · linarith only [h152, h30, hlam]
                                                          · linarith only [h151, h9, hlam]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h9, hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h30, hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h34, hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [h35, hlam, p121_0]
                                                        · obtain ⟨p121_0, p121_1, p121_2, p121_3⟩ := h121c
                                                          linarith only [hlam, p121_0]
                                                      · rcases h4bigk with h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h10, h13, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p161_1, u4elo0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h31, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p161_1, u4elo0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [hc34, hlam, hphi, p161_1, u4elo0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          rcases p161_3 (m.d 0 4) (by simp) with h166 | h166
                                                          · rcases p161_3 (m.d 1 4) (by simp) with h167 | h167
                                                            · linarith only [h167, h2, hlam]
                                                            · linarith only [h167, h30, hlam]
                                                          · linarith only [h166, hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h2, hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h31, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p161_1, u4elo1]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h13, hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          rcases p161_3 (m.d 0 4) (by simp) with h175 | h175
                                                          · rcases p161_3 (m.d 1 4) (by simp) with h176 | h176
                                                            · rcases p161_3 (m.d 2 4) (by simp) with h177 | h177
                                                              · linarith only [h11, h177, hlam]
                                                              · linarith only [h177, h34, hlam]
                                                            · linarith only [h176, hlam, p161_0]
                                                          · linarith only [h175, h9, hlam]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h5, hlam, p161_1]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h11, hlam, p161_1]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h31, hlam, p161_1]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h0, h11, hc01, hc45, hlam, hphi, ht0b, ht5b, p161_1]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h7, hlam, p161_1]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [hc14, hlam, hphi, p161_1, u4elo3]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h7, hc24, hlam, hphi, p161_1, u4elo0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          rcases p161_3 (m.d 0 4) (by simp) with h191 | h191
                                                          · rcases p161_3 (m.d 1 4) (by simp) with h192 | h192
                                                            · linarith only [h13, h192, hlam]
                                                            · linarith only [h192, h30, hlam]
                                                          · linarith only [h191, h9, hlam]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h9, hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h30, hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h34, hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [h35, hlam, p161_0]
                                                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                                                          linarith only [hlam, p161_0]
                                                      · linarith only [h80, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h80, hlam, ht01, ht12, ht23, ht34, p36_1, u4elo0]
                                                  · linarith only [h77, h9, hlam]
                                                · linarith only [h76, h8, hlam]
                                              · linarith only [h6, h75, hlam]
                                            · linarith only [h3, h74, hlam]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h3, hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h6, hlam, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h8, hlam, p36_0]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [h9, hlam, p36_1]
                                          · obtain ⟨p36_0, p36_1, p36_2, p36_3⟩ := h36c
                                            linarith only [hlam, p36_0]
                                        · linarith only [h35, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h30, h31, h33, h34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                                    · linarith only [h33, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h13, h29, h30, h7, hc14, hc35, hlam, hphi, u4elo0, u5elo4]
                              · linarith only [h29, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h12, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h220 | h220
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h222 | h222
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h226 | h226
                                      · linarith only [h0, h10, h219, h226, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h223, h224, h226, hc34, hlam, hphi, u4elo1]
                                    · linarith only [h10, h225, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h10, h224, hc12, hlam, hphi, ht23, ht34, u4elo3]
                                · linarith only [h223, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h10, h219, h222, hc24, hlam, hphi, ht45, u5elo3]
                            · linarith only [h10, h219, h221, hc24, hlam, hphi, u4elo3]
                          · linarith only [h219, h220, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h241 | h241
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h242 | h242
                                        · rcases h0bigk with h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h1, h236, h242, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h1, h236, h242, hc01, hc45, hlam, hphi, ht0b, ht5b, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h219, h235, h240, h242, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            rcases p243_3 (m.d 0 1) (by simp) with h248 | h248
                                            · rcases p243_3 (m.d 0 2) (by simp) with h249 | h249
                                              · linarith only [h0, h249, hlam]
                                              · linarith only [h249, h6, hlam]
                                            · linarith only [h248, h3, hlam]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h0, hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h219, h235, h240, h242, h5, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h0, h219, h235, h240, h242, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            rcases p243_3 (m.d 0 1) (by simp) with h257 | h257
                                            · rcases p243_3 (m.d 0 2) (by simp) with h258 | h258
                                              · rcases p243_3 (m.d 0 3) (by simp) with h259 | h259
                                                · linarith only [h259, h4, hlam]
                                                · linarith only [h259, h8, hlam]
                                              · linarith only [h258, h6, hlam]
                                            · linarith only [h257, h3, hlam]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h1, hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h4, hlam, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h219, h235, h240, h242, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            rcases p243_3 (m.d 0 1) (by simp) with h268 | h268
                                            · rcases p243_3 (m.d 0 2) (by simp) with h269 | h269
                                              · rcases p243_3 (m.d 0 3) (by simp) with h270 | h270
                                                · rcases p243_3 (m.d 0 4) (by simp) with h271 | h271
                                                  · linarith only [h271, h7, hlam]
                                                  · linarith only [h271, h9, hlam]
                                                · linarith only [h270, h8, hlam]
                                              · linarith only [h269, h6, hlam]
                                            · linarith only [h268, h3, hlam]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h2, hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h5, hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h7, hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            rcases p243_3 (m.d 0 1) (by simp) with h281 | h281
                                            · rcases p243_3 (m.d 0 2) (by simp) with h282 | h282
                                              · rcases p243_3 (m.d 0 3) (by simp) with h283 | h283
                                                · rcases p243_3 (m.d 0 4) (by simp) with h284 | h284
                                                  · rcases p243_3 (m.d 0 5) (by simp) with h285 | h285
                                                    · linarith only [h285, h9, hlam]
                                                    · rcases h0emin with h287 | h287 | h287 | h287 | h287
                                                      · rcases h4bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h219, h235, h240, h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p288_1, u4elo0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h219, h235, h240, h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p288_1, u4elo0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p288_1, u4elo0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          rcases p288_3 (m.d 0 4) (by simp) with h293 | h293
                                                          · rcases p288_3 (m.d 1 4) (by simp) with h294 | h294
                                                            · linarith only [h2, h294, hlam]
                                                            · linarith only [h238, h294, hlam]
                                                          · linarith only [h293, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h2, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h219, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p288_1, u4elo1]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          rcases p288_3 (m.d 0 4) (by simp) with h302 | h302
                                                          · rcases p288_3 (m.d 1 4) (by simp) with h303 | h303
                                                            · rcases p288_3 (m.d 2 4) (by simp) with h304 | h304
                                                              · rcases p288_3 (m.d 3 4) (by simp) with h305 | h305
                                                                · linarith only [h236, h305, hlam]
                                                                · linarith only [h242, h305, hlam]
                                                              · linarith only [h241, h304, hlam]
                                                            · linarith only [h303, hlam, p288_0]
                                                          · linarith only [h302, h9, hlam]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h5, hlam, p288_1]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [hc14, hlam, hphi, p288_1, u4elo2]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p288_1, u4elo2]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          rcases p288_3 (m.d 0 4) (by simp) with h315 | h315
                                                          · rcases p288_3 (m.d 1 4) (by simp) with h316 | h316
                                                            · linarith only [h219, h316, hlam]
                                                            · linarith only [h238, h316, hlam]
                                                          · linarith only [h315, h9, hlam]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h7, hlam, p288_1]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h236, hlam, p288_1]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h239, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h1, h236, hc01, hc45, hlam, hphi, ht0b, ht5b, p288_1]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h9, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h238, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h241, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [h242, hlam, p288_0]
                                                        · obtain ⟨p288_0, p288_1, p288_2, p288_3⟩ := h288c
                                                          linarith only [hlam, p288_0]
                                                      · rcases h4bigk with h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h219, h235, h240, h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p330_1, u4elo0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hc24, hlam, hphi, p330_1, u4elo0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hc34, hlam, hphi, p330_1, u4elo0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          rcases p330_3 (m.d 0 4) (by simp) with h335 | h335
                                                          · rcases p330_3 (m.d 1 4) (by simp) with h336 | h336
                                                            · linarith only [h2, h336, hlam]
                                                            · linarith only [h238, h336, hlam]
                                                          · linarith only [h335, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h2, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h219, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p330_1, u4elo1]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          rcases p330_3 (m.d 0 4) (by simp) with h344 | h344
                                                          · rcases p330_3 (m.d 1 4) (by simp) with h345 | h345
                                                            · rcases p330_3 (m.d 2 4) (by simp) with h346 | h346
                                                              · rcases p330_3 (m.d 3 4) (by simp) with h347 | h347
                                                                · linarith only [h236, h347, hlam]
                                                                · linarith only [h242, h347, hlam]
                                                              · linarith only [h241, h346, hlam]
                                                            · linarith only [h345, hlam, p330_0]
                                                          · linarith only [h344, h9, hlam]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h5, hlam, p330_1]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hc14, hlam, hphi, p330_1, u4elo2]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p330_1, u4elo2]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          rcases p330_3 (m.d 0 4) (by simp) with h357 | h357
                                                          · rcases p330_3 (m.d 1 4) (by simp) with h358 | h358
                                                            · linarith only [h219, h358, hlam]
                                                            · linarith only [h238, h358, hlam]
                                                          · linarith only [h357, h9, hlam]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h7, hlam, p330_1]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h236, hlam, p330_1]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h239, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h0, h10, h236, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p330_1]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h9, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h238, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h241, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [h242, hlam, p330_0]
                                                        · obtain ⟨p330_0, p330_1, p330_2, p330_3⟩ := h330c
                                                          linarith only [hlam, p330_0]
                                                      · rcases h4bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h219, h235, h240, h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p372_1, u4elo0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [hc24, hlam, hphi, p372_1, u4elo0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [hc34, hlam, hphi, p372_1, u4elo0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          rcases p372_3 (m.d 0 4) (by simp) with h377 | h377
                                                          · rcases p372_3 (m.d 1 4) (by simp) with h378 | h378
                                                            · linarith only [h2, h378, hlam]
                                                            · linarith only [h238, h378, hlam]
                                                          · linarith only [h377, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h2, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h219, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p372_1, u4elo1]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          rcases p372_3 (m.d 0 4) (by simp) with h386 | h386
                                                          · rcases p372_3 (m.d 1 4) (by simp) with h387 | h387
                                                            · rcases p372_3 (m.d 2 4) (by simp) with h388 | h388
                                                              · rcases p372_3 (m.d 3 4) (by simp) with h389 | h389
                                                                · linarith only [h236, h389, hlam]
                                                                · linarith only [h242, h389, hlam]
                                                              · linarith only [h241, h388, hlam]
                                                            · linarith only [h387, hlam, p372_0]
                                                          · linarith only [h386, h9, hlam]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h5, hlam, p372_1]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h5, hc14, hlam, hphi, p372_1, u4elo0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h242, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p372_1, u4elo0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          rcases p372_3 (m.d 0 4) (by simp) with h399 | h399
                                                          · rcases p372_3 (m.d 1 4) (by simp) with h400 | h400
                                                            · linarith only [h219, h400, hlam]
                                                            · linarith only [h238, h400, hlam]
                                                          · linarith only [h399, h9, hlam]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h7, hlam, p372_1]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h236, hlam, p372_1]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h239, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h0, h10, h236, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p372_1]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h9, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h238, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h241, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [h242, hlam, p372_0]
                                                        · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                                          linarith only [hlam, p372_0]
                                                      · linarith only [h287, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h287, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                                  · linarith only [h284, h9, hlam]
                                                · linarith only [h283, h8, hlam]
                                              · linarith only [h282, h6, hlam]
                                            · linarith only [h281, h3, hlam]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h3, hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h6, hlam, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h8, hlam, p243_0]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [h9, hlam, p243_1]
                                          · obtain ⟨p243_0, p243_1, p243_2, p243_3⟩ := h243c
                                            linarith only [hlam, p243_0]
                                        · linarith only [h219, h235, h242, h5, hc25, hc34, hlam, hphi, u4elo0, u5elo4]
                                      · linarith only [h219, h235, h240, h241, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                    · linarith only [h10, h240, hc13, hlam, hphi, ht34, ht45, u5elo3]
                                  · linarith only [h10, h235, h236, h239, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h219, h235, h238, hc25, hlam, hphi, u5elo4]
                              · linarith only [h219, h235, h237, h5, hc13, hc25, hlam, hphi, ht34, u4elo0, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h431 | h431
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h432 | h432
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                                  · linarith only [h0, h10, h235, h236, h4, h433, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h10, h235, h433, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                                · linarith only [h10, h235, h236, h432, hc25, hlam, hphi, u5elo4]
                              · linarith only [h10, h235, h431, hc25, hlam, hphi, u5elo3]
                          · linarith only [h235, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h444 | h444
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h445 | h445
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                            · linarith only [h1, h446, h7, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                                  · linarith only [h1, h443, h450, h7, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                                        · rcases h0bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h0, h444, h450, h452, h454, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            rcases p455_3 (m.d 0 1) (by simp) with h458 | h458
                                            · rcases p455_3 (m.d 0 2) (by simp) with h459 | h459
                                              · linarith only [h0, h459, hlam]
                                              · linarith only [h4, h459, hlam]
                                            · linarith only [h1, h458, hlam]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            rcases p455_3 (m.d 0 1) (by simp) with h463 | h463
                                            · rcases p455_3 (m.d 0 2) (by simp) with h464 | h464
                                              · linarith only [h0, h464, hlam]
                                              · linarith only [h464, h5, hlam]
                                            · linarith only [h2, h463, hlam]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            rcases p455_3 (m.d 0 1) (by simp) with h468 | h468
                                            · rcases p455_3 (m.d 0 2) (by simp) with h469 | h469
                                              · linarith only [h0, h469, hlam]
                                              · linarith only [h469, h6, hlam]
                                            · linarith only [h3, h468, hlam]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h0, hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            rcases p455_3 (m.d 0 1) (by simp) with h475 | h475
                                            · rcases p455_3 (m.d 0 2) (by simp) with h476 | h476
                                              · rcases p455_3 (m.d 0 3) (by simp) with h477 | h477
                                                · linarith only [h4, h477, hlam]
                                                · rcases p455_3 (m.d 0 4) (by simp) with h479 | h479
                                                  · linarith only [h479, h5, hlam]
                                                  · linarith only [h479, h7, hlam]
                                              · linarith only [h4, h476, hlam]
                                            · linarith only [h1, h475, hlam]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            rcases p455_3 (m.d 0 1) (by simp) with h484 | h484
                                            · rcases p455_3 (m.d 0 2) (by simp) with h485 | h485
                                              · rcases p455_3 (m.d 0 3) (by simp) with h486 | h486
                                                · linarith only [h4, h486, hlam]
                                                · rcases p455_3 (m.d 0 4) (by simp) with h488 | h488
                                                  · linarith only [h488, h5, hlam]
                                                  · rcases p455_3 (m.d 0 5) (by simp) with h490 | h490
                                                    · linarith only [h490, h6, hlam]
                                                    · rcases h0emin with h492 | h492 | h492 | h492 | h492
                                                      · rcases h4bigk with h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h443, h446, h452, h454, hc02, hc45, hlam, hphi, ht0b, ht5b, p455_1, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h0, h450, h452, h454, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h7, hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h2, hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h450, h452, h454, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p493_1, u4elo1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h446, hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h0, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h5, hlam, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h444, hlam, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h450, hlam, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h0, h444, hc01, hc45, hlam, hphi, ht0b, ht5b, p493_1]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hc04, hlam, hphi, p493_1, u4elo3]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hc14, hlam, hphi, p493_1, u4elo3]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hc24, hlam, hphi, p493_1, u4elo3]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          rcases p493_3 (m.d 0 4) (by simp) with h513 | h513
                                                          · linarith only [h513, h7, hlam]
                                                          · linarith only [h442, h513, hlam]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h442, hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h449, hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h453, hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [h454, hlam, p493_0]
                                                        · obtain ⟨p493_0, p493_1, p493_2, p493_3⟩ := h493c
                                                          linarith only [hlam, p493_0]
                                                      · rcases h4bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h443, h446, h452, h454, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p521_1, u4elo0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h0, h450, h452, h454, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1, p521_1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h7, hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1, p521_1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h2, hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h450, h452, h454, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p521_1, u4elo1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h446, hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h0, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1, p521_1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h5, hlam, p521_1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h444, hlam, p521_1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h450, hlam, p521_1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p455_1, p521_1]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hc04, hlam, hphi, p521_1, u4elo3]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hc14, hlam, hphi, p521_1, u4elo3]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hc24, hlam, hphi, p521_1, u4elo3]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          rcases p521_3 (m.d 0 4) (by simp) with h541 | h541
                                                          · linarith only [h541, h7, hlam]
                                                          · linarith only [h442, h541, hlam]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h442, hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h449, hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h453, hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [h454, hlam, p521_0]
                                                        · obtain ⟨p521_0, p521_1, p521_2, p521_3⟩ := h521c
                                                          linarith only [hlam, p521_0]
                                                      · linarith only [h492, h7, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h492, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h492, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                              · linarith only [h485, h5, hlam]
                                            · linarith only [h2, h484, hlam]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            rcases p455_3 (m.d 0 1) (by simp) with h554 | h554
                                            · rcases p455_3 (m.d 0 2) (by simp) with h555 | h555
                                              · rcases p455_3 (m.d 0 3) (by simp) with h556 | h556
                                                · linarith only [h4, h556, hlam]
                                                · linarith only [h441, h556, hlam]
                                              · linarith only [h555, h6, hlam]
                                            · linarith only [h3, h554, hlam]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h1, hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h4, hlam, p455_1]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h7, hlam, p455_1]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p455_1, u4elo3]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h2, hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h5, hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h7, hc03, hlam, hphi, ht34, p455_1, u4elo3]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            rcases p455_3 (m.d 0 1) (by simp) with h570 | h570
                                            · rcases p455_3 (m.d 0 2) (by simp) with h571 | h571
                                              · rcases p455_3 (m.d 0 3) (by simp) with h572 | h572
                                                · linarith only [h572, h7, hlam]
                                                · linarith only [h441, h572, hlam]
                                              · linarith only [h571, h6, hlam]
                                            · linarith only [h3, h570, hlam]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h3, hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h6, hlam, p455_1]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h441, hlam, p455_0]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [h442, hlam, p455_1]
                                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                                            linarith only [hlam, p455_0]
                                        · linarith only [h454, h7, hc04, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h3, h449, h450, h452, h453, hc35, hlam, hphi, u5elo0]
                                    · linarith only [h452, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h446, h448, h449, hc35, hlam, hphi, u5elo4]
                              · linarith only [h448, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h445, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h443, h444, h5, hc23, hlam, hphi, ht34, u4elo0]
                      · linarith only [h4, h443, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h442, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h441, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h594 | h594
            · rcases m.htr 0 2 5 (by decide) (by decide) with h595 | h595
              · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
                · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h598 | h598
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h599 | h599
                      · linarith only [h0, h4, h594, h599, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h601 | h601
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h604 | h604
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h605 | h605
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h606 | h606
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h607 | h607
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h608 | h608
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h609 | h609
                                        · rcases h0bigk with h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h0, h601, h606, h609, hc01, hc45, hlam, hphi, ht0b, ht5b, p610_1]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h0, h4, h601, h606, h609, hc01, hc45, hlam, hphi, ht0b, ht5b, p610_1]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            rcases p610_3 (m.d 0 1) (by simp) with h614 | h614
                                            · rcases p610_3 (m.d 0 2) (by simp) with h615 | h615
                                              · linarith only [h0, h615, hlam]
                                              · linarith only [h594, h615, hlam]
                                            · linarith only [h2, h614, hlam]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            rcases p610_3 (m.d 0 1) (by simp) with h619 | h619
                                            · rcases p610_3 (m.d 0 2) (by simp) with h620 | h620
                                              · linarith only [h0, h620, hlam]
                                              · linarith only [h595, h620, hlam]
                                            · linarith only [h3, h619, hlam]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h0, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h4, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h2, h4, h601, h606, h609, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p610_1]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            rcases p610_3 (m.d 0 1) (by simp) with h628 | h628
                                            · rcases p610_3 (m.d 0 2) (by simp) with h629 | h629
                                              · rcases p610_3 (m.d 0 3) (by simp) with h630 | h630
                                                · rcases p610_3 (m.d 0 4) (by simp) with h631 | h631
                                                  · linarith only [h594, h631, hlam]
                                                  · linarith only [h598, h631, hlam]
                                                · linarith only [h597, h630, hlam]
                                              · linarith only [h595, h629, hlam]
                                            · linarith only [h3, h628, hlam]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h1, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h0, h601, h606, h609, hc03, hc45, hlam, hphi, ht0b, ht5b, p610_1]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            rcases p610_3 (m.d 0 1) (by simp) with h640 | h640
                                            · rcases p610_3 (m.d 0 2) (by simp) with h641 | h641
                                              · linarith only [h4, h641, hlam]
                                              · linarith only [h594, h641, hlam]
                                            · linarith only [h2, h640, hlam]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            rcases p610_3 (m.d 0 1) (by simp) with h645 | h645
                                            · rcases p610_3 (m.d 0 2) (by simp) with h646 | h646
                                              · linarith only [h4, h646, hlam]
                                              · linarith only [h595, h646, hlam]
                                            · linarith only [h3, h645, hlam]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h2, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h594, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h596, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            rcases p610_3 (m.d 0 1) (by simp) with h654 | h654
                                            · rcases p610_3 (m.d 0 2) (by simp) with h655 | h655
                                              · rcases p610_3 (m.d 0 3) (by simp) with h656 | h656
                                                · rcases p610_3 (m.d 0 4) (by simp) with h657 | h657
                                                  · rcases p610_3 (m.d 0 5) (by simp) with h658 | h658
                                                    · linarith only [h598, h658, hlam]
                                                    · rcases h0emin with h660 | h660 | h660 | h660 | h660
                                                      · rcases h4bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h601, h606, h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p661_1, u4elo0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h606, h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p661_1, u4elo0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p661_1, u4elo0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          rcases p661_3 (m.d 0 4) (by simp) with h666 | h666
                                                          · rcases p661_3 (m.d 1 4) (by simp) with h667 | h667
                                                            · linarith only [h2, h667, hlam]
                                                            · linarith only [h605, h667, hlam]
                                                          · linarith only [h666, hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h2, hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h606, h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p661_1, u4elo1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p661_1, u4elo1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          rcases p661_3 (m.d 0 4) (by simp) with h675 | h675
                                                          · rcases p661_3 (m.d 1 4) (by simp) with h676 | h676
                                                            · rcases p661_3 (m.d 2 4) (by simp) with h677 | h677
                                                              · linarith only [h601, h677, hlam]
                                                              · linarith only [h608, h677, hlam]
                                                            · linarith only [h676, hlam, p661_0]
                                                          · linarith only [h598, h675, hlam]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h594, hlam, p661_1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h601, hlam, p661_1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p661_1, u4elo2]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h0, h601, hc01, hc45, hlam, hphi, ht0b, ht5b, p661_1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h596, hlam, p661_1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h603, hlam, p661_1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h606, hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h1, h603, hc01, hc45, hlam, hphi, ht0b, ht5b, p661_1]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h598, hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h605, hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h608, hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [h609, hlam, p661_0]
                                                        · obtain ⟨p661_0, p661_1, p661_2, p661_3⟩ := h661c
                                                          linarith only [hlam, p661_0]
                                                      · linarith only [h4, h660, hc23, hlam, ht01, ht12]
                                                      · rcases h4bigk with h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hc14, hlam, hphi, p698_1, u4elo0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hc24, hlam, hphi, p698_1, u4elo0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hc34, hlam, hphi, p698_1, u4elo0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          rcases p698_3 (m.d 0 4) (by simp) with h703 | h703
                                                          · rcases p698_3 (m.d 1 4) (by simp) with h704 | h704
                                                            · linarith only [h2, h704, hlam]
                                                            · linarith only [h605, h704, hlam]
                                                          · linarith only [h703, hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h2, hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h606, h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p698_1, u4elo1]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h2, h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p698_1, u4elo0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          rcases p698_3 (m.d 0 4) (by simp) with h712 | h712
                                                          · rcases p698_3 (m.d 1 4) (by simp) with h713 | h713
                                                            · rcases p698_3 (m.d 2 4) (by simp) with h714 | h714
                                                              · linarith only [h601, h714, hlam]
                                                              · linarith only [h608, h714, hlam]
                                                            · linarith only [h713, hlam, p698_0]
                                                          · linarith only [h598, h712, hlam]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h594, hlam, p698_1]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h601, hlam, p698_1]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h609, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p698_1, u4elo2]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h0, h4, h601, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p698_1]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h596, hlam, p698_1]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h603, hlam, p698_1]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h606, hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h1, h603, hc01, hc45, hlam, hphi, ht0b, ht5b, p698_1]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h598, hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h605, hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h608, hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [h609, hlam, p698_0]
                                                        · obtain ⟨p698_0, p698_1, p698_2, p698_3⟩ := h698c
                                                          linarith only [hlam, p698_0]
                                                      · linarith only [h660, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h660, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                                  · linarith only [h598, h657, hlam]
                                                · linarith only [h597, h656, hlam]
                                              · linarith only [h595, h655, hlam]
                                            · linarith only [h3, h654, hlam]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h3, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h595, hlam, p610_1]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h597, hlam, p610_0]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [h598, hlam, p610_1]
                                          · obtain ⟨p610_0, p610_1, p610_2, p610_3⟩ := h610c
                                            linarith only [hlam, p610_0]
                                        · linarith only [h609, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h605, h608, hc24, hlam, hphi, ht45, u5elo1]
                                    · linarith only [h4, h607, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h4, h606, hc02, hlam, hphi, ht23, ht34, u4elo3]
                                · linarith only [h598, h603, h605, hc34, hlam, hphi, u4elo0]
                              · linarith only [h604, hc13, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h599, h601, h603, hc24, hlam, hphi, u4elo3]
                          · linarith only [h601, h602, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h4, h594, h601, hc12, hc23, hlam, hphi]
                    · linarith only [h598, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h4, h597, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h4, h594, h596, hc24, hlam, hphi, u4elo3]
              · linarith only [h594, h595, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h758 | h758
              · rcases m.htr 0 3 4 (by decide) (by decide) with h759 | h759
                · rcases m.htr 0 3 5 (by decide) (by decide) with h760 | h760
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h761 | h761
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h762 | h762
                      · linarith only [h0, h594, h762, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h764 | h764
                        · linarith only [h0, h594, h764, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h766 | h766
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h768 | h768
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h769 | h769
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h770 | h770
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h772 | h772
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h773 | h773
                                        · rcases h0bigk with h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            rcases p774_3 (m.d 0 1) (by simp) with h776 | h776
                                            · rcases p774_3 (m.d 0 2) (by simp) with h777 | h777
                                              · linarith only [h0, h777, hlam]
                                              · rcases p774_3 (m.d 0 3) (by simp) with h779 | h779
                                                · linarith only [h1, h779, hlam]
                                                · linarith only [h4, h779, hlam]
                                            · linarith only [h0, h776, hlam]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h1, h767, h773, hc01, hc45, hlam, hphi, ht0b, ht5b, p774_1]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            rcases p774_3 (m.d 0 1) (by simp) with h784 | h784
                                            · rcases p774_3 (m.d 0 2) (by simp) with h785 | h785
                                              · linarith only [h0, h785, hlam]
                                              · rcases p774_3 (m.d 0 3) (by simp) with h787 | h787
                                                · linarith only [h1, h787, hlam]
                                                · linarith only [h759, h787, hlam]
                                            · linarith only [h2, h784, hlam]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            rcases p774_3 (m.d 0 1) (by simp) with h791 | h791
                                            · rcases p774_3 (m.d 0 2) (by simp) with h792 | h792
                                              · linarith only [h0, h792, hlam]
                                              · linarith only [h758, h792, hlam]
                                            · linarith only [h3, h791, hlam]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h0, hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h4, hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h594, hlam, p774_1]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h594, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p774_1, u4elo2]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h1, hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            rcases p774_3 (m.d 0 1) (by simp) with h802 | h802
                                            · rcases p774_3 (m.d 0 2) (by simp) with h803 | h803
                                              · linarith only [h4, h803, hlam]
                                              · rcases p774_3 (m.d 0 3) (by simp) with h805 | h805
                                                · rcases p774_3 (m.d 0 4) (by simp) with h806 | h806
                                                  · linarith only [h759, h806, hlam]
                                                  · linarith only [h594, h806, hlam]
                                                · linarith only [h4, h805, hlam]
                                            · linarith only [h0, h802, hlam]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            rcases p774_3 (m.d 0 1) (by simp) with h812 | h812
                                            · rcases p774_3 (m.d 0 2) (by simp) with h813 | h813
                                              · linarith only [h4, h813, hlam]
                                              · rcases p774_3 (m.d 0 3) (by simp) with h815 | h815
                                                · rcases p774_3 (m.d 0 4) (by simp) with h816 | h816
                                                  · linarith only [h759, h816, hlam]
                                                  · rcases p774_3 (m.d 0 5) (by simp) with h818 | h818
                                                    · linarith only [h760, h818, hlam]
                                                    · rcases h0emin with h820 | h820 | h820 | h820 | h820
                                                      · rcases h4bigk with h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h764, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p774_1, p821_1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h594, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h4, h773, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p774_1, p821_1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p774_1, p821_1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h2, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h764, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h773, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p821_1, u4elo1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h2, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p774_1, p821_1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [hc04, hlam, hphi, p821_1, u4elo2]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [hc14, hlam, hphi, p821_1, u4elo2]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h773, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p821_1, u4elo2]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          rcases p821_3 (m.d 0 4) (by simp) with h836 | h836
                                                          · linarith only [h594, h836, hlam]
                                                          · linarith only [h761, h836, hlam]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h759, hlam, p821_1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h767, hlam, p821_1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h770, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h1, h767, hc01, hc45, hlam, hphi, ht0b, ht5b, p821_1]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h761, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h769, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h772, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [h773, hlam, p821_0]
                                                        · obtain ⟨p821_0, p821_1, p821_2, p821_3⟩ := h821c
                                                          linarith only [hlam, p821_0]
                                                      · linarith only [h594, h820, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · rcases h4bigk with h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p774_1, p850_1]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h594, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h0, h4, h594, h766, h771, h773, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p774_1, p850_1, u4elo2]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p774_1, p850_1]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h2, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h764, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hc34, hlam, hphi, p850_1, u4elo1]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h2, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p774_1, p850_1]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hc04, hlam, hphi, p850_1, u4elo2]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hc14, hlam, hphi, p850_1, u4elo2]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hc34, hlam, hphi, p850_1, u4elo2]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          rcases p850_3 (m.d 0 4) (by simp) with h865 | h865
                                                          · linarith only [h594, h865, hlam]
                                                          · linarith only [h761, h865, hlam]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h759, hlam, p850_1]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h767, hlam, p850_1]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h770, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h4, h759, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p774_1, p850_1]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h761, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h769, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h772, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [h773, hlam, p850_0]
                                                        · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                                          linarith only [hlam, p850_0]
                                                      · linarith only [h820, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h820, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                                · linarith only [h759, h815, hlam]
                                            · linarith only [h2, h812, hlam]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            rcases p774_3 (m.d 0 1) (by simp) with h882 | h882
                                            · rcases p774_3 (m.d 0 2) (by simp) with h883 | h883
                                              · linarith only [h4, h883, hlam]
                                              · linarith only [h758, h883, hlam]
                                            · linarith only [h3, h882, hlam]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h2, hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h0, h594, h766, h771, h773, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p774_1, u4elo2]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h759, hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            rcases p774_3 (m.d 0 1) (by simp) with h891 | h891
                                            · rcases p774_3 (m.d 0 2) (by simp) with h892 | h892
                                              · linarith only [h594, h892, hlam]
                                              · linarith only [h758, h892, hlam]
                                            · linarith only [h3, h891, hlam]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h3, hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h758, hlam, p774_1]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h760, hlam, p774_0]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [h761, hlam, p774_1]
                                          · obtain ⟨p774_0, p774_1, p774_2, p774_3⟩ := h774c
                                            linarith only [hlam, p774_0]
                                        · linarith only [h773, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h594, h772, hc02, hlam, hphi, ht23, ht34, u4elo4]
                                    · linarith only [h4, h771, hc03, hlam, hphi, ht34, ht45, u5elo3]
                                  · linarith only [h0, h4, h766, h770, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                                · linarith only [h764, h766, h769, hc25, hlam, hphi, u5elo4]
                              · linarith only [h768, hc13, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h907 | h907
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h908 | h908
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h909 | h909
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h910 | h910
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h911 | h911
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h912 | h912
                                        · rcases h0bigk with h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            rcases p913_3 (m.d 0 1) (by simp) with h915 | h915
                                            · rcases p913_3 (m.d 0 2) (by simp) with h916 | h916
                                              · linarith only [h0, h916, hlam]
                                              · rcases p913_3 (m.d 0 3) (by simp) with h918 | h918
                                                · linarith only [h1, h918, hlam]
                                                · linarith only [h4, h918, hlam]
                                            · linarith only [h0, h915, hlam]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h759, h762, h766, h767, h910, h912, hc01, hc45, hlam, hphi, ht0b, ht5b, p913_1]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h759, h762, h766, h767, h910, h912, hc01, hc45, hlam, hphi, ht0b, ht5b, p913_1]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            rcases p913_3 (m.d 0 1) (by simp) with h924 | h924
                                            · rcases p913_3 (m.d 0 2) (by simp) with h925 | h925
                                              · linarith only [h0, h925, hlam]
                                              · linarith only [h758, h925, hlam]
                                            · linarith only [h3, h924, hlam]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h0, hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h4, hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h594, hlam, p913_1]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h594, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p913_1, u4elo2]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h1, hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            rcases p913_3 (m.d 0 1) (by simp) with h935 | h935
                                            · rcases p913_3 (m.d 0 2) (by simp) with h936 | h936
                                              · linarith only [h4, h936, hlam]
                                              · rcases p913_3 (m.d 0 3) (by simp) with h938 | h938
                                                · rcases p913_3 (m.d 0 4) (by simp) with h939 | h939
                                                  · linarith only [h759, h939, hlam]
                                                  · linarith only [h594, h939, hlam]
                                                · linarith only [h4, h938, hlam]
                                            · linarith only [h0, h935, hlam]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h759, h762, h766, h767, h910, h912, hc03, hc45, hlam, hphi, ht0b, ht5b, p913_1]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            rcases p913_3 (m.d 0 1) (by simp) with h946 | h946
                                            · rcases p913_3 (m.d 0 2) (by simp) with h947 | h947
                                              · linarith only [h4, h947, hlam]
                                              · linarith only [h758, h947, hlam]
                                            · linarith only [h3, h946, hlam]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h2, hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [hc02, hlam, hphi, ht23, ht34, p913_1, u4elo0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h759, hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            rcases p913_3 (m.d 0 1) (by simp) with h955 | h955
                                            · rcases p913_3 (m.d 0 2) (by simp) with h956 | h956
                                              · linarith only [h594, h956, hlam]
                                              · linarith only [h758, h956, hlam]
                                            · linarith only [h3, h955, hlam]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h3, hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h758, hlam, p913_1]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h760, hlam, p913_0]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [h761, hlam, p913_1]
                                          · obtain ⟨p913_0, p913_1, p913_2, p913_3⟩ := h913c
                                            linarith only [hlam, p913_0]
                                        · linarith only [h762, h766, h767, h910, h912, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                      · linarith only [h3, h594, h762, h766, h767, h908, h910, h911, hc04, hc35, hlam, hphi, u4elo3, u5elo0]
                                    · linarith only [h594, h759, h762, h766, h767, h910, hc23, hc25, hlam, hphi, ht34, u4elo2, u5elo3]
                                  · linarith only [h4, h759, h909, hlam]
                                · linarith only [h762, h766, h767, h908, hc25, hlam, hphi, u5elo4]
                              · linarith only [h762, h766, h907, hc25, hlam, hphi, u5elo3]
                          · linarith only [h766, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h761, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h760, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h974 | h974
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h975 | h975
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h976 | h976
                      · linarith only [h0, h4, h758, h976, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h978 | h978
                        · linarith only [h0, h594, h978, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h980 | h980
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
                            · linarith only [h0, h1, h4, h759, h980, h981, hc01, hc25, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h983 | h983
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h985 | h985
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h986 | h986
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h987 | h987
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h988 | h988
                                        · rcases h0bigk with h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            rcases p989_3 (m.d 0 1) (by simp) with h991 | h991
                                            · rcases p989_3 (m.d 0 2) (by simp) with h992 | h992
                                              · linarith only [h0, h992, hlam]
                                              · rcases p989_3 (m.d 0 3) (by simp) with h994 | h994
                                                · linarith only [h1, h994, hlam]
                                                · linarith only [h4, h994, hlam]
                                            · linarith only [h0, h991, hlam]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            rcases p989_3 (m.d 0 1) (by simp) with h998 | h998
                                            · rcases p989_3 (m.d 0 2) (by simp) with h999 | h999
                                              · linarith only [h0, h999, hlam]
                                              · rcases p989_3 (m.d 0 3) (by simp) with h1001 | h1001
                                                · linarith only [h1, h1001, hlam]
                                                · rcases p989_3 (m.d 0 4) (by simp) with h1003 | h1003
                                                  · linarith only [h1003, h2, hlam]
                                                  · linarith only [h1003, h759, hlam]
                                            · linarith only [h1, h998, hlam]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            rcases p989_3 (m.d 0 1) (by simp) with h1007 | h1007
                                            · rcases p989_3 (m.d 0 2) (by simp) with h1008 | h1008
                                              · linarith only [h0, h1008, hlam]
                                              · rcases p989_3 (m.d 0 3) (by simp) with h1010 | h1010
                                                · linarith only [h1, h1010, hlam]
                                                · rcases p989_3 (m.d 0 4) (by simp) with h1012 | h1012
                                                  · linarith only [h1012, h2, hlam]
                                                  · rcases p989_3 (m.d 0 5) (by simp) with h1014 | h1014
                                                    · linarith only [h1014, h3, hlam]
                                                    · rcases h0emin with h1016 | h1016 | h1016 | h1016 | h1016
                                                      · rcases h4bigk with h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c | h1017c
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h976, h980, h981, h986, h988, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1017_1, u4elo0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h594, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h759, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p1017_1, p989_1]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h2, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h978, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h981, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1017_1, p989_1]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hc04, hlam, hphi, p1017_1, u4elo2]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hc14, hlam, hphi, p1017_1, u4elo2]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h0, h4, h759, h980, h986, h988, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1017_1, u4elo2]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          rcases p1017_3 (m.d 0 4) (by simp) with h1032 | h1032
                                                          · linarith only [h1032, h594, hlam]
                                                          · linarith only [h1032, h975, hlam]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h0, h4, h759, h980, h985, h986, h988, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1017_1]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h976, h980, h981, h986, h988, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1017_1, u4elo3]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h985, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          rcases p1017_3 (m.d 0 4) (by simp) with h1039 | h1039
                                                          · linarith only [h1039, h759, hlam]
                                                          · linarith only [h1039, h975, hlam]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h975, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h984, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h987, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [h988, hlam, p1017_0]
                                                        · obtain ⟨p1017_0, p1017_1, p1017_2, p1017_3⟩ := h1017c
                                                          linarith only [hlam, p1017_0]
                                                      · linarith only [h1016, h4, h759, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h1016, h759, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h1016, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h1016, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                            · linarith only [h1007, h2, hlam]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            rcases p989_3 (m.d 0 1) (by simp) with h1052 | h1052
                                            · rcases p989_3 (m.d 0 2) (by simp) with h1053 | h1053
                                              · linarith only [h0, h1053, hlam]
                                              · linarith only [h1053, h758, hlam]
                                            · linarith only [h1052, h3, hlam]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h0, hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h4, hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h594, hlam, p989_1]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h4, h759, h985, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p989_1, u4elo2]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h1, hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h759, h985, hc02, hlam, hphi, ht23, ht34, p989_1, u4elo2]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h759, hlam, p989_1]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h759, h985, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p989_1, u4elo2]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h2, hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h759, h985, hc02, hlam, hphi, ht23, ht34, p989_1, u4elo2]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h759, h985, hc03, hlam, hphi, ht34, p989_1, u4elo2]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            rcases p989_3 (m.d 0 1) (by simp) with h1071 | h1071
                                            · rcases p989_3 (m.d 0 2) (by simp) with h1072 | h1072
                                              · linarith only [h1072, h594, hlam]
                                              · linarith only [h1072, h758, hlam]
                                            · linarith only [h1071, h3, hlam]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h3, hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h758, hlam, p989_1]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h974, hlam, p989_0]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [h975, hlam, p989_1]
                                          · obtain ⟨p989_0, p989_1, p989_2, p989_3⟩ := h989c
                                            linarith only [hlam, p989_0]
                                        · linarith only [h759, h988, hc04, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h0, h3, h4, h759, h980, h984, h985, h986, h987, hc35, hlam, hphi, u5elo0]
                                    · linarith only [h0, h4, h759, h980, h985, h986, hc23, hc25, hlam, hphi, ht34, u4elo2, u5elo3]
                                  · linarith only [h0, h4, h980, h985, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                                · linarith only [h984, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h4, h759, h980, h983, hc13, hc25, hlam, hphi, ht34, u4elo3, u5elo3]
                          · linarith only [h980, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h4, h758, h759, h975, hc04, hc25, hlam, hphi, u4elo3, u5elo4]
                  · linarith only [h4, h758, h974, hc25, hlam, hphi, u5elo3]
              · linarith only [h758, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1093 | h1093
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1094 | h1094
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1095 | h1095
          · linarith only [h0, h1, h1095, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1097 | h1097
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1098 | h1098
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1099 | h1099
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1100 | h1100
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1101 | h1101
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
                      · linarith only [h0, h1, h1095, h1102, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1104 | h1104
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1105 | h1105
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1106 | h1106
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1107 | h1107
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1108 | h1108
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1110 | h1110
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1111 | h1111
                                      · linarith only [h0, h1, h1102, h1104, h1111, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                      · linarith only [h1109, h1111, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h1, h1102, h1104, h1109, h1110, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · linarith only [h0, h1, h1102, h1104, h1109, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h1108, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h1, h1104, h1107, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h1104, h1106, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1104, h1105, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h1, h1097, h1102, h1104, hc12, hc23, hlam, hphi]
                    · linarith only [h1101, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1, h1100, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h1099, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h1097, h1098, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1125 | h1125
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1126 | h1126
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1127 | h1127
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1128 | h1128
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1129 | h1129
                      · linarith only [h0, h1097, h1129, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1131 | h1131
                        · linarith only [h0, h1097, h1131, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1135 | h1135
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1136 | h1136
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1137 | h1137
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1138 | h1138
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1139 | h1139
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1140 | h1140
                                        · rcases h0bigk with h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h0, h1, h1133, h1138, h1140, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1141_1]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1, hlam, p1141_1]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h0, h1, h1097, h1129, h1133, h1138, h1140, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1141_1]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            rcases p1141_3 (m.d 0 1) (by simp) with h1146 | h1146
                                            · rcases p1141_3 (m.d 0 2) (by simp) with h1147 | h1147
                                              · linarith only [h0, h1147, hlam]
                                              · linarith only [h1125, h1147, hlam]
                                            · linarith only [h1094, h1146, hlam]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h0, hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1095, hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1097, hlam, p1141_1]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1097, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1141_1, u4elo2]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h0, h1133, hc03, hc25, hlam, hphi, ht0b, ht5b, p1141_1]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            rcases p1141_3 (m.d 0 1) (by simp) with h1157 | h1157
                                            · linarith only [h1, h1157, hlam]
                                            · linarith only [h0, h1157, hlam]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            rcases p1141_3 (m.d 0 1) (by simp) with h1161 | h1161
                                            · linarith only [h1, h1161, hlam]
                                            · linarith only [h1093, h1161, hlam]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            rcases p1141_3 (m.d 0 1) (by simp) with h1164 | h1164
                                            · linarith only [h1, h1164, hlam]
                                            · linarith only [h1094, h1164, hlam]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1093, hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h0, h1133, h1138, h1140, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1141_1, u4elo0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1126, hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            rcases p1141_3 (m.d 0 1) (by simp) with h1171 | h1171
                                            · rcases p1141_3 (m.d 0 2) (by simp) with h1172 | h1172
                                              · linarith only [h1097, h1172, hlam]
                                              · linarith only [h1125, h1172, hlam]
                                            · linarith only [h1094, h1171, hlam]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1094, hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1125, hlam, p1141_1]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1127, hlam, p1141_0]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [h1128, hlam, p1141_1]
                                          · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                            linarith only [hlam, p1141_0]
                                        · linarith only [h1140, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h0, h1097, h1133, h1138, h1139, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                    · linarith only [h1, h1093, h1129, h1136, h1138, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · linarith only [h1, h1093, h1129, h1131, h1133, h1137, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1131, h1133, h1136, hc25, hlam, hphi, u5elo4]
                              · linarith only [h1, h1093, h1131, h1133, h1135, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h1093, h1131, h1133, h1134, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1133, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h1128, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1127, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1, h1093, h1126, hc14, hlam, hphi, u4elo3]
              · linarith only [h1125, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h1094, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h1093, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1195 | h1195
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1196 | h1196
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1197 | h1197
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1198 | h1198
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1199 | h1199
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1200 | h1200
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1201 | h1201
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1202 | h1202
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1203 | h1203
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1204 | h1204
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1205 | h1205
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1206 | h1206
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1207 | h1207
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1208 | h1208
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1209 | h1209
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1210 | h1210
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1211 | h1211
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1212 | h1212
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1213 | h1213
                                        · linarith only [h0, h1195, h1204, h1210, h1213, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                        · linarith only [h1196, h1205, h1212, h1213, hc34, hlam, hphi, u4elo0]
                                      · linarith only [h0, h1195, h1207, h1209, h1212, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h1211, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                  · linarith only [h0, h1195, h1207, h1210, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h1209, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h1208, hc13, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1221 | h1221
                              · linarith only [h0, h1195, h1201, h1207, h1221, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1221, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h1206, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1205, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h1195, h1198, h1201, h1204, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1203, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1201, h1202, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1229 | h1229
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1230 | h1230
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1231 | h1231
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1232 | h1232
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1233 | h1233
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1234 | h1234
                            · linarith only [h1195, h1201, h1234, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1236 | h1236
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1238 | h1238
                                  · linarith only [h0, h1195, h1198, h1201, h1236, h1238, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1240 | h1240
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1241 | h1241
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1242 | h1242
                                        · rcases h0bigk with h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h0, hlam, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h0, h1195, h1231, h1240, h1242, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h0, h1195, h1201, h1231, h1240, h1242, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            rcases p1243_3 (m.d 0 1) (by simp) with h1248 | h1248
                                            · rcases p1243_3 (m.d 0 2) (by simp) with h1249 | h1249
                                              · rcases p1243_3 (m.d 0 3) (by simp) with h1250 | h1250
                                                · linarith only [h1195, h1250, hlam]
                                                · linarith only [h1229, h1250, hlam]
                                              · linarith only [h1200, h1249, hlam]
                                            · linarith only [h1197, h1248, hlam]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h0, h1195, h1231, h1240, h1242, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            rcases p1243_3 (m.d 0 1) (by simp) with h1257 | h1257
                                            · linarith only [h0, h1257, hlam]
                                            · linarith only [h1195, h1257, hlam]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            rcases p1243_3 (m.d 0 1) (by simp) with h1260 | h1260
                                            · linarith only [h0, h1260, hlam]
                                            · linarith only [h1196, h1260, hlam]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            rcases p1243_3 (m.d 0 1) (by simp) with h1263 | h1263
                                            · linarith only [h0, h1263, hlam]
                                            · linarith only [h1197, h1263, hlam]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1195, hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1198, hlam, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1201, hlam, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1197, h1201, h1233, h1240, h1242, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1243_1, u4elo3]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1196, hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1199, hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [hc03, hlam, hphi, ht34, p1243_1, u4elo0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            rcases p1243_3 (m.d 0 1) (by simp) with h1275 | h1275
                                            · rcases p1243_3 (m.d 0 2) (by simp) with h1276 | h1276
                                              · rcases p1243_3 (m.d 0 3) (by simp) with h1277 | h1277
                                                · linarith only [h1201, h1277, hlam]
                                                · linarith only [h1229, h1277, hlam]
                                              · linarith only [h1200, h1276, hlam]
                                            · linarith only [h1197, h1275, hlam]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1197, hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1200, hlam, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1229, hlam, p1243_0]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [h1230, hlam, p1243_1]
                                          · obtain ⟨p1243_0, p1243_1, p1243_2, p1243_3⟩ := h1243c
                                            linarith only [hlam, p1243_0]
                                        · linarith only [h1201, h1242, hc04, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h0, h1196, h1237, h1241, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h1195, h1201, h1236, h1240, hc23, hlam, hphi, ht34, u4elo3]
                                · linarith only [h1195, h1201, h1236, h1237, hc14, hc35, hlam, hphi, u4elo3, u5elo4]
                              · linarith only [h1236, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h1233, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1195, h1231, h1232, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h1198, h1231, hlam]
                    · linarith only [h1201, h1229, h1230, hc35, hlam, hphi, u5elo4]
                  · linarith only [h1229, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1200, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1195, h1199, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h1195, h1198, hlam]
        · linarith only [h1195, h1197, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · linarith only [h1195, h1196, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1302 | h1302
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1303 | h1303
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1304 | h1304
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1305 | h1305
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1306 | h1306
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1307 | h1307
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1308 | h1308
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1309 | h1309
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1310 | h1310
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1311 | h1311
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1312 | h1312
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1313 | h1313
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1314 | h1314
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1315 | h1315
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1316 | h1316
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1317 | h1317
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1318 | h1318
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1319 | h1319
                                        · rcases h0bigk with h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c | h1320c
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h0, hlam, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1195, hlam, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1195, h1302, h1310, h1311, h1316, h1319, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            rcases p1320_3 (m.d 0 1) (by simp) with h1325 | h1325
                                            · rcases p1320_3 (m.d 0 2) (by simp) with h1326 | h1326
                                              · rcases p1320_3 (m.d 0 3) (by simp) with h1327 | h1327
                                                · rcases p1320_3 (m.d 0 4) (by simp) with h1328 | h1328
                                                  · linarith only [h1302, h1328, hlam]
                                                  · linarith only [h1309, h1328, hlam]
                                                · linarith only [h1308, h1327, hlam]
                                              · linarith only [h1306, h1326, hlam]
                                            · linarith only [h1303, h1325, hlam]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h0, h1302, h1311, h1316, h1319, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h0, h1195, h1302, h1311, h1316, h1319, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            rcases p1320_3 (m.d 0 1) (by simp) with h1337 | h1337
                                            · linarith only [h0, h1337, hlam]
                                            · linarith only [h1302, h1337, hlam]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            rcases p1320_3 (m.d 0 1) (by simp) with h1340 | h1340
                                            · linarith only [h0, h1340, hlam]
                                            · linarith only [h1303, h1340, hlam]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1302, h1311, h1316, h1319, hc03, hc45, hlam, hphi, ht0b, ht5b, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1304, hlam, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            rcases p1320_3 (m.d 0 1) (by simp) with h1346 | h1346
                                            · linarith only [h1195, h1346, hlam]
                                            · linarith only [h1302, h1346, hlam]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            rcases p1320_3 (m.d 0 1) (by simp) with h1349 | h1349
                                            · linarith only [h1195, h1349, hlam]
                                            · linarith only [h1303, h1349, hlam]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1302, hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1305, hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1307, hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            rcases p1320_3 (m.d 0 1) (by simp) with h1356 | h1356
                                            · rcases p1320_3 (m.d 0 2) (by simp) with h1357 | h1357
                                              · rcases p1320_3 (m.d 0 3) (by simp) with h1358 | h1358
                                                · rcases p1320_3 (m.d 0 4) (by simp) with h1359 | h1359
                                                  · rcases p1320_3 (m.d 0 5) (by simp) with h1360 | h1360
                                                    · linarith only [h1309, h1360, hlam]
                                                    · rcases h0emin with h1362 | h1362 | h1362 | h1362 | h1362
                                                      · linarith only [h0, h1362, hc12, hlam, ht01]
                                                      · rcases h4bigk with h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1311, h1316, h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1364_1, u4elo0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1316, h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1364_1, u4elo0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1364_1, u4elo0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          rcases p1364_3 (m.d 0 4) (by simp) with h1369 | h1369
                                                          · rcases p1364_3 (m.d 1 4) (by simp) with h1370 | h1370
                                                            · linarith only [h1302, h1370, hlam]
                                                            · linarith only [h1315, h1370, hlam]
                                                          · linarith only [h1369, hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1302, hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1316, h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1364_1, u4elo1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1195, h1302, h1310, h1319, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1195, h1302, h1310, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1305, hlam, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1311, hlam, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1364_1, u4elo2]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1195, h1302, h1310, h1311, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1307, hlam, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1313, hlam, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1316, hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h0, h1304, h1316, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1364_1]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1309, hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1315, hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1318, hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [h1319, hlam, p1364_0]
                                                        · obtain ⟨p1364_0, p1364_1, p1364_2, p1364_3⟩ := h1364c
                                                          linarith only [hlam, p1364_0]
                                                      · rcases h4bigk with h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [hc14, hlam, hphi, p1394_1, u4elo0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1316, hc34, hlam, hphi, p1394_1, u4elo0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [hc34, hlam, hphi, p1394_1, u4elo0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          rcases p1394_3 (m.d 0 4) (by simp) with h1399 | h1399
                                                          · rcases p1394_3 (m.d 1 4) (by simp) with h1400 | h1400
                                                            · linarith only [h1302, h1400, hlam]
                                                            · linarith only [h1315, h1400, hlam]
                                                          · linarith only [h1399, hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1302, hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1316, h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1394_1, u4elo1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1195, h1302, h1310, h1319, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1195, h1302, h1310, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1305, hlam, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1311, hlam, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1394_1, u4elo2]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1195, h1302, h1310, h1311, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1307, hlam, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1313, hlam, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1316, hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1195, h1302, h1310, h1313, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1309, hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1315, hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1318, hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [h1319, hlam, p1394_0]
                                                        · obtain ⟨p1394_0, p1394_1, p1394_2, p1394_3⟩ := h1394c
                                                          linarith only [hlam, p1394_0]
                                                      · linarith only [h1362, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h1362, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                                  · linarith only [h1309, h1359, hlam]
                                                · linarith only [h1308, h1358, hlam]
                                              · linarith only [h1306, h1357, hlam]
                                            · linarith only [h1303, h1356, hlam]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1303, hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1306, hlam, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1308, hlam, p1320_0]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [h1309, hlam, p1320_1]
                                          · obtain ⟨p1320_0, p1320_1, p1320_2, p1320_3⟩ := h1320c
                                            linarith only [hlam, p1320_0]
                                        · linarith only [h1319, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h1195, h1302, h1310, h1315, h1318, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h1317, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1438 | h1438
                                    · linarith only [h1195, h1302, h1310, h1313, h1316, h1438, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h1438, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h1309, h1315, hc14, hlam, hphi, ht45, u5elo0]
                              · linarith only [h1195, h1314, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1195, h1302, h1311, h1313, hc24, hlam, hphi, u4elo3]
                          · linarith only [h1195, h1302, h1310, h1311, h1312, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h1195, h1310, h1311, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h1302, h1304, h1309, h1310, hc02, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1309, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1308, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1195, h1302, h1307, hc14, hlam, hphi, u4elo3]
              · linarith only [h1306, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1195, h1302, h1304, h1305, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1452 | h1452
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1453 | h1453
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1454 | h1454
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1455 | h1455
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1456 | h1456
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1457 | h1457
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1458 | h1458
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1459 | h1459
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1460 | h1460
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1461 | h1461
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1462 | h1462
                                · linarith only [h0, h1302, h1304, h1457, h1462, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1456, h1462, hc14, hlam, hphi, u4elo0]
                              · linarith only [h0, h1304, h1457, h1461, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h0, h1303, h1304, h1454, h1457, h1460, hc03, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h1302, h1304, h1457, h1458, h1459, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1302, h1304, h1457, h1458, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1469 | h1469
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1470 | h1470
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1471 | h1471
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1472 | h1472
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1473 | h1473
                                · linarith only [h0, h1302, h1457, h1473, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h1473, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h1195, h1472, hc03, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h1302, h1457, h1469, h1471, hc24, hlam, hphi, u4elo3]
                          · linarith only [h0, h1302, h1469, h1470, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h1302, h1469, hc14, hlam, hphi, u4elo2]
                    · linarith only [h1456, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1455, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h1302, h1304, h1454, hc14, hlam, hphi, u4elo3]
              · linarith only [h0, h1302, h1453, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h1302, h1452, hc14, hlam, hphi, u4elo2]
        · linarith only [h1302, h1303, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1486 | h1486
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1487 | h1487
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1488 | h1488
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1489 | h1489
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1490 | h1490
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1491 | h1491
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1492 | h1492
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1493 | h1493
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1494 | h1494
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1495 | h1495
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1496 | h1496
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1497 | h1497
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1498 | h1498
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1499 | h1499
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1500 | h1500
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1501 | h1501
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1502 | h1502
                                        · rcases h0bigk with h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h0, hlam, p1503_1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1195, hlam, p1503_1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1302, hlam, p1503_1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1302, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1503_1, u4elo1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            rcases p1503_3 (m.d 0 1) (by simp) with h1509 | h1509
                                            · linarith only [h0, h1509, hlam]
                                            · rcases p1503_3 (m.d 0 2) (by simp) with h1511 | h1511
                                              · rcases p1503_3 (m.d 0 3) (by simp) with h1512 | h1512
                                                · linarith only [h1487, h1512, hlam]
                                                · linarith only [h1195, h1512, hlam]
                                              · linarith only [h0, h1511, hlam]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h0, h1487, h1499, h1502, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            rcases p1503_3 (m.d 0 1) (by simp) with h1518 | h1518
                                            · linarith only [h0, h1518, hlam]
                                            · rcases p1503_3 (m.d 0 2) (by simp) with h1520 | h1520
                                              · rcases p1503_3 (m.d 0 3) (by simp) with h1521 | h1521
                                                · linarith only [h1487, h1521, hlam]
                                                · linarith only [h1490, h1521, hlam]
                                              · linarith only [h1488, h1520, hlam]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            rcases p1503_3 (m.d 0 1) (by simp) with h1525 | h1525
                                            · linarith only [h0, h1525, hlam]
                                            · linarith only [h1486, h1525, hlam]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            rcases p1503_3 (m.d 0 1) (by simp) with h1528 | h1528
                                            · linarith only [h1195, h1528, hlam]
                                            · rcases p1503_3 (m.d 0 2) (by simp) with h1530 | h1530
                                              · rcases p1503_3 (m.d 0 3) (by simp) with h1531 | h1531
                                                · rcases p1503_3 (m.d 0 4) (by simp) with h1532 | h1532
                                                  · linarith only [h1490, h1532, hlam]
                                                  · linarith only [h1302, h1532, hlam]
                                                · linarith only [h1195, h1531, hlam]
                                              · linarith only [h0, h1530, hlam]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1487, hlam, p1503_1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            rcases p1503_3 (m.d 0 1) (by simp) with h1539 | h1539
                                            · linarith only [h1195, h1539, hlam]
                                            · rcases p1503_3 (m.d 0 2) (by simp) with h1541 | h1541
                                              · rcases p1503_3 (m.d 0 3) (by simp) with h1542 | h1542
                                                · rcases p1503_3 (m.d 0 4) (by simp) with h1543 | h1543
                                                  · linarith only [h1490, h1543, hlam]
                                                  · rcases p1503_3 (m.d 0 5) (by simp) with h1545 | h1545
                                                    · linarith only [h1491, h1545, hlam]
                                                    · rcases h0emin with h1547 | h1547 | h1547 | h1547 | h1547
                                                      · linarith only [h1302, h1547, hlam, ht01, ht12, ht23, ht34, u4elo1]
                                                      · rcases h4bigk with h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1302, hlam, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1302, h1486, h1487, h1495, h1500, h1502, hc02, hc24, hc45, hlam, hphi, ht0b, ht5b, p1503_1, p1549_1, u4elo1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h0, h1487, h1502, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h0, h1487, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [hc04, hlam, hphi, p1549_1, u4elo1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [hc24, hlam, hphi, p1549_1, u4elo1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1502, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1549_1, u4elo1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          rcases p1549_3 (m.d 0 4) (by simp) with h1559 | h1559
                                                          · linarith only [h1302, h1559, hlam]
                                                          · linarith only [h1492, h1559, hlam]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1488, hlam, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1494, hlam, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1502, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1549_1, u4elo2]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h0, h1487, h1488, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1490, hlam, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1496, hlam, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1499, hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h0, h1487, h1499, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1549_1]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1492, hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1498, hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1501, hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [h1502, hlam, p1549_0]
                                                        · obtain ⟨p1549_0, p1549_1, p1549_2, p1549_3⟩ := h1549c
                                                          linarith only [hlam, p1549_0]
                                                      · rcases h4bigk with h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1302, hlam, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h0, h1487, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1503_1, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h0, h1302, h1486, h1487, h1495, h1500, h1502, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1, p1577_1, u4elo1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h0, h1487, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [hc04, hlam, hphi, p1577_1, u4elo1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1499, hc34, hlam, hphi, p1577_1, u4elo1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [hc34, hlam, hphi, p1577_1, u4elo1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          rcases p1577_3 (m.d 0 4) (by simp) with h1587 | h1587
                                                          · linarith only [h1302, h1587, hlam]
                                                          · linarith only [h1492, h1587, hlam]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1488, hlam, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1494, hlam, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1502, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1577_1, u4elo2]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h0, h1487, h1488, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1490, hlam, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1496, hlam, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1499, hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h0, h1487, h1490, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1503_1, p1577_1]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1492, hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1498, hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1501, hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [h1502, hlam, p1577_0]
                                                        · obtain ⟨p1577_0, p1577_1, p1577_2, p1577_3⟩ := h1577c
                                                          linarith only [hlam, p1577_0]
                                                      · linarith only [h0, h1487, h1547, hc12, hlam, ht01, p1503_1]
                                                      · linarith only [h1547, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                                · linarith only [h1490, h1542, hlam]
                                              · linarith only [h1488, h1541, hlam]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            rcases p1503_3 (m.d 0 1) (by simp) with h1609 | h1609
                                            · linarith only [h1195, h1609, hlam]
                                            · linarith only [h1486, h1609, hlam]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1486, h1495, h1500, h1502, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1503_1, u4elo0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1488, hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1490, hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            rcases p1503_3 (m.d 0 1) (by simp) with h1616 | h1616
                                            · linarith only [h1302, h1616, hlam]
                                            · linarith only [h1486, h1616, hlam]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1486, hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1489, hlam, p1503_1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1491, hlam, p1503_0]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [h1492, hlam, p1503_1]
                                          · obtain ⟨p1503_0, p1503_1, p1503_2, p1503_3⟩ := h1503c
                                            linarith only [hlam, p1503_0]
                                        · linarith only [h1502, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h1486, h1498, h1501, hc24, hlam, hphi, ht45, u5elo0]
                                    · linarith only [h1500, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1627 | h1627
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1628 | h1628
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1629 | h1629
                                        · rcases h0bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h0, hlam, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1195, hlam, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1302, hlam, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1302, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1630_1, u4elo1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            rcases p1630_3 (m.d 0 1) (by simp) with h1636 | h1636
                                            · linarith only [h0, h1636, hlam]
                                            · rcases p1630_3 (m.d 0 2) (by simp) with h1638 | h1638
                                              · rcases p1630_3 (m.d 0 3) (by simp) with h1639 | h1639
                                                · linarith only [h1487, h1639, hlam]
                                                · linarith only [h1195, h1639, hlam]
                                              · linarith only [h0, h1638, hlam]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h0, h1490, h1499, h1627, h1629, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h0, h1490, h1499, h1627, h1629, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            rcases p1630_3 (m.d 0 1) (by simp) with h1646 | h1646
                                            · linarith only [h0, h1646, hlam]
                                            · linarith only [h1486, h1646, hlam]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            rcases p1630_3 (m.d 0 1) (by simp) with h1649 | h1649
                                            · linarith only [h1195, h1649, hlam]
                                            · rcases p1630_3 (m.d 0 2) (by simp) with h1651 | h1651
                                              · rcases p1630_3 (m.d 0 3) (by simp) with h1652 | h1652
                                                · rcases p1630_3 (m.d 0 4) (by simp) with h1653 | h1653
                                                  · linarith only [h1490, h1653, hlam]
                                                  · linarith only [h1302, h1653, hlam]
                                                · linarith only [h1195, h1652, hlam]
                                              · linarith only [h0, h1651, hlam]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1487, hlam, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1490, h1499, h1627, h1629, hc03, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            rcases p1630_3 (m.d 0 1) (by simp) with h1661 | h1661
                                            · linarith only [h1195, h1661, hlam]
                                            · linarith only [h1486, h1661, hlam]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1486, h1495, h1627, h1629, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1630_1, u4elo0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1488, hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1490, hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            rcases p1630_3 (m.d 0 1) (by simp) with h1668 | h1668
                                            · linarith only [h1302, h1668, hlam]
                                            · linarith only [h1486, h1668, hlam]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1486, hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1489, hlam, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1491, hlam, p1630_0]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [h1492, hlam, p1630_1]
                                          · obtain ⟨p1630_0, p1630_1, p1630_2, p1630_3⟩ := h1630c
                                            linarith only [hlam, p1630_0]
                                        · linarith only [h1499, h1627, h1629, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                      · linarith only [h1628, hc24, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1627, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h1302, h1498, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                              · linarith only [h1195, h1497, hc03, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h1195, h1486, h1490, h1495, h1496, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h1495, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1195, h1486, h1493, h1494, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                      · linarith only [h0, h1487, h1493, hlam]
                    · linarith only [h1302, h1486, h1492, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1491, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1687 | h1687
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1688 | h1688
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1689 | h1689
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1690 | h1690
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1691 | h1691
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1692 | h1692
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1693 | h1693
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1694 | h1694
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1695 | h1695
                                  · linarith only [h1487, h1490, h1695, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1697 | h1697
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1698 | h1698
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1699 | h1699
                                        · rcases h0bigk with h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c | h1700c
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h0, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1195, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1302, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1195, h1490, h1692, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1700_1, u4elo1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 1) (by simp) with h1706 | h1706
                                            · linarith only [h0, h1706, hlam]
                                            · rcases p1700_3 (m.d 0 2) (by simp) with h1708 | h1708
                                              · rcases p1700_3 (m.d 0 3) (by simp) with h1709 | h1709
                                                · linarith only [h1487, h1709, hlam]
                                                · linarith only [h1195, h1709, hlam]
                                              · linarith only [h0, h1708, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 1) (by simp) with h1714 | h1714
                                            · linarith only [h0, h1714, hlam]
                                            · rcases p1700_3 (m.d 0 2) (by simp) with h1716 | h1716
                                              · rcases p1700_3 (m.d 0 3) (by simp) with h1717 | h1717
                                                · linarith only [h1487, h1717, hlam]
                                                · rcases p1700_3 (m.d 0 4) (by simp) with h1719 | h1719
                                                  · linarith only [h1488, h1719, hlam]
                                                  · linarith only [h1490, h1719, hlam]
                                              · linarith only [h1487, h1716, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 1) (by simp) with h1723 | h1723
                                            · linarith only [h0, h1723, hlam]
                                            · rcases p1700_3 (m.d 0 2) (by simp) with h1725 | h1725
                                              · rcases p1700_3 (m.d 0 3) (by simp) with h1726 | h1726
                                                · linarith only [h1487, h1726, hlam]
                                                · rcases p1700_3 (m.d 0 4) (by simp) with h1728 | h1728
                                                  · linarith only [h1488, h1728, hlam]
                                                  · rcases p1700_3 (m.d 0 5) (by simp) with h1730 | h1730
                                                    · linarith only [h1489, h1730, hlam]
                                                    · rcases h0emin with h1732 | h1732 | h1732 | h1732 | h1732
                                                      · linarith only [h1195, h1490, h1692, h1732, hlam, ht01, ht12, ht23, ht34, u4elo1]
                                                      · rcases h4bigk with h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1302, hlam, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p1700_1, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1490, hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1700_1, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hc04, hlam, hphi, p1734_1, u4elo1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hc24, hlam, hphi, p1734_1, u4elo1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1195, h1486, h1490, h1691, h1697, h1699, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1734_1, u4elo1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          rcases p1734_3 (m.d 0 4) (by simp) with h1744 | h1744
                                                          · linarith only [h1302, h1744, hlam]
                                                          · linarith only [h1688, h1744, hlam]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1488, hlam, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1690, hlam, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1695, hlam, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h0, h1488, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1700_1, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hc04, hlam, hphi, p1734_1, u4elo3]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1692, hlam, p1734_1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1692, hc24, hlam, hphi, p1734_1, u4elo1]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          rcases p1734_3 (m.d 0 4) (by simp) with h1756 | h1756
                                                          · linarith only [h1490, h1756, hlam]
                                                          · linarith only [h1688, h1756, hlam]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1688, hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1694, hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1698, hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [h1699, hlam, p1734_0]
                                                        · obtain ⟨p1734_0, p1734_1, p1734_2, p1734_3⟩ := h1734c
                                                          linarith only [hlam, p1734_0]
                                                      · linarith only [h1490, h1732, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h1732, hlam, ht01, ht12, ht23, ht34, u4elo0]
                                                      · linarith only [h1732, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                              · linarith only [h1488, h1725, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 1) (by simp) with h1768 | h1768
                                            · linarith only [h0, h1768, hlam]
                                            · linarith only [h1486, h1768, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1486, h1490, h1691, h1692, h1697, h1699, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1700_1, u4elo1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1487, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1490, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1490, h1692, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1700_1, u4elo1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1486, h1490, h1691, h1692, h1697, h1699, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1700_1, u4elo1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1488, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1490, h1692, hc03, hlam, hphi, ht34, p1700_1, u4elo1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            rcases p1700_3 (m.d 0 1) (by simp) with h1780 | h1780
                                            · linarith only [h1302, h1780, hlam]
                                            · linarith only [h1486, h1780, hlam]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1486, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1489, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1687, hlam, p1700_0]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [h1688, hlam, p1700_1]
                                          · obtain ⟨p1700_0, p1700_1, p1700_2, p1700_3⟩ := h1700c
                                            linarith only [hlam, p1700_0]
                                        · linarith only [h1490, h1699, hc04, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h1195, h1486, h1490, h1692, h1694, h1698, hc24, hlam, hphi, u4elo1]
                                    · linarith only [h1195, h1486, h1490, h1691, h1692, h1697, hc23, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                                · linarith only [h1195, h1486, h1490, h1691, h1692, h1694, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                              · linarith only [h1195, h1486, h1490, h1691, h1692, h1693, hc13, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                            · linarith only [h1195, h1486, h1691, h1692, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h1691, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1195, h1486, h1488, h1689, h1690, hc02, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1487, h1689, hlam]
                    · linarith only [h1195, h1486, h1490, h1688, hc04, hc15, hlam, hphi, u4elo3, u5elo4]
                  · linarith only [h1195, h1486, h1687, hc15, hlam, hphi, u5elo3]
              · linarith only [h1489, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1487, h1488, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1801 | h1801
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1802 | h1802
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1803 | h1803
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1804 | h1804
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1805 | h1805
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1806 | h1806
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1807 | h1807
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1808 | h1808
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1809 | h1809
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1810 | h1810
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1811 | h1811
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1812 | h1812
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1813 | h1813
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1814 | h1814
                                      · linarith only [h1487, h1801, h1806, h1814, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h1814, hc24, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1302, h1486, h1487, h1801, h1808, h1812, h1813, hc25, hc34, hlam, hphi, u4elo1, u5elo3]
                                  · linarith only [h1487, h1801, h1812, hc24, hlam, hphi, u4elo3]
                                · linarith only [h1302, h1486, h1808, h1811, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                              · linarith only [h1302, h1486, h1808, h1810, hc13, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                            · linarith only [h1487, h1801, h1803, h1806, h1809, hlam]
                          · linarith only [h1302, h1486, h1487, h1801, h1806, h1808, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1487, h1801, h1806, h1807, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1824 | h1824
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1825 | h1825
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1826 | h1826
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1827 | h1827
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1828 | h1828
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1829 | h1829
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1830 | h1830
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1831 | h1831
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1832 | h1832
                                        · rcases h0bigk with h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c | h1833c
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h0, hlam, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1195, hlam, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1302, hlam, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1302, h1806, h1824, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h0, h1806, hc01, hc23, hlam, hphi, ht12, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1487, hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h0, h1302, h1486, h1806, h1825, h1830, h1832, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            rcases p1833_3 (m.d 0 1) (by simp) with h1843 | h1843
                                            · linarith only [h0, h1843, hlam]
                                            · linarith only [h1486, h1843, hlam]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            rcases p1833_3 (m.d 0 1) (by simp) with h1846 | h1846
                                            · linarith only [h1195, h1846, hlam]
                                            · rcases p1833_3 (m.d 0 2) (by simp) with h1848 | h1848
                                              · linarith only [h1487, h1848, hlam]
                                              · linarith only [h0, h1848, hlam]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1195, h1801, h1806, h1829, h1832, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            rcases p1833_3 (m.d 0 1) (by simp) with h1853 | h1853
                                            · linarith only [h1195, h1853, hlam]
                                            · rcases p1833_3 (m.d 0 2) (by simp) with h1855 | h1855
                                              · linarith only [h1487, h1855, hlam]
                                              · linarith only [h1801, h1855, hlam]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            rcases p1833_3 (m.d 0 1) (by simp) with h1858 | h1858
                                            · linarith only [h1195, h1858, hlam]
                                            · linarith only [h1486, h1858, hlam]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1486, h1825, h1830, h1832, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1833_1, u4elo0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1801, hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1803, hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            rcases p1833_3 (m.d 0 1) (by simp) with h1865 | h1865
                                            · linarith only [h1302, h1865, hlam]
                                            · linarith only [h1486, h1865, hlam]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1486, hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1802, hlam, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1804, hlam, p1833_0]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [h1805, hlam, p1833_1]
                                          · obtain ⟨p1833_0, p1833_1, p1833_2, p1833_3⟩ := h1833c
                                            linarith only [hlam, p1833_0]
                                        · linarith only [h1832, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h1302, h1486, h1828, h1831, hc24, hlam, hphi, u4elo1]
                                    · linarith only [h0, h1806, h1830, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h1302, h1806, h1824, h1829, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1302, h1486, h1825, h1828, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                              · linarith only [h1195, h1302, h1486, h1825, h1827, hc03, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                            · linarith only [h1302, h1486, h1803, h1806, h1824, h1825, h1826, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1302, h1486, h1824, h1825, hc15, hlam, hphi, u5elo2]
                        · linarith only [h0, h1486, h1824, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h1302, h1486, h1805, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1804, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1487, h1801, h1803, hc24, hlam, hphi, u4elo3]
              · linarith only [h1801, h1802, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1886 | h1886
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1887 | h1887
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1888 | h1888
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1889 | h1889
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1890 | h1890
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1891 | h1891
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1892 | h1892
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1893 | h1893
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1894 | h1894
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1895 | h1895
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1896 | h1896
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1897 | h1897
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1898 | h1898
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1899 | h1899
                                        · rcases h0bigk with h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h0, hlam, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1195, hlam, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1302, hlam, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1302, h1486, h1892, h1897, h1899, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1900_1, u4elo1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1487, h1890, hc01, hc12, hlam, hphi, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1487, hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1801, hlam, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1486, h1801, h1891, h1892, h1897, h1899, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1900_1, u4elo1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1486, h1487, h1890, h1892, h1897, h1899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h0, h1486, h1487, h1890, h1892, h1897, h1899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1302, h1486, h1487, h1890, h1892, h1897, h1899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            rcases p1900_3 (m.d 0 1) (by simp) with h1915 | h1915
                                            · linarith only [h1195, h1915, hlam]
                                            · linarith only [h1486, h1915, hlam]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1486, h1892, h1897, h1899, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1900_1, u4elo0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h0, h1486, h1801, h1891, h1892, h1897, h1899, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1900_1, u4elo1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1887, hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            rcases p1900_3 (m.d 0 1) (by simp) with h1922 | h1922
                                            · linarith only [h1302, h1922, hlam]
                                            · linarith only [h1486, h1922, hlam]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1486, hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1886, hlam, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1888, hlam, p1900_0]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [h1889, hlam, p1900_1]
                                          · obtain ⟨p1900_0, p1900_1, p1900_2, p1900_3⟩ := h1900c
                                            linarith only [hlam, p1900_0]
                                        · linarith only [h1899, hc34, hlam, hphi, ht45, u5elo4]
                                      · linarith only [h0, h1486, h1801, h1895, h1898, hlam]
                                    · linarith only [h1487, h1897, hc03, hlam, hphi, ht34, ht45, u5elo3]
                                  · linarith only [h1487, h1896, hc02, hlam, hphi, ht23, ht34, u4elo3]
                                · linarith only [h1895, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h1486, h1801, h1891, h1892, h1894, hc13, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                            · linarith only [h1487, h1887, h1890, h1893, hlam]
                          · linarith only [h0, h1486, h1801, h1891, h1892, hc12, hc15, hlam, hphi, ht23, ht34, u4elo1, u5elo2]
                        · linarith only [h0, h1486, h1487, h1890, h1891, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1939 | h1939
                        · linarith only [h0, h1486, h1801, h1890, h1939, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1486, h1939, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h1889, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1486, h1801, h1888, hc03, hc15, hlam, hphi, ht34, u4elo2, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1944 | h1944
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1945 | h1945
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1946 | h1946
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1947 | h1947
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1948 | h1948
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1949 | h1949
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1950 | h1950
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1951 | h1951
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1952 | h1952
                                  · linarith only [h0, h1486, h1487, h1887, h1946, h1948, h1952, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h1486, h1487, h1948, h1949, h1952, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                                · linarith only [h1951, hc14, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h1486, h1487, h1887, h1948, h1949, h1950, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1195, h1486, h1948, h1949, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h1486, h1801, h1948, hc12, hc15, hlam, hphi, ht23, ht34, u4elo2, u5elo2]
                        · linarith only [h1946, h1947, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1960 | h1960
                        · linarith only [h0, h1486, h1801, h1946, h1960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1486, h1960, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h1945, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1486, h1487, h1944, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h1486, h1886, hc15, hlam, hphi, u5elo2]
        · linarith only [h1486, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

end R2N4
