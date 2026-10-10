import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT3_H_I_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc05 := m.hcor 0 5 (by decide)
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
  have h5bigk := hb5.1
  have h3elo := hb3.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
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
    rcases p0_3 (m.d 0 5) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 5) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 5) (by simp) with h6 | h6
          · linarith only [h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 5 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 2 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 0 2 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h11, h5, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h14, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h14, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h13, h17, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h17, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h20 | h20
                  · linarith only [h20, h5, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h23, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h23, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h22, h26, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h26, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
              · rcases m.htr 0 2 3 (by decide) (by decide) with h31 | h31
                · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h32, h5, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h35, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h35, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h38 | h38
                      · linarith only [h34, h38, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h38, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h41, h5, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h44, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h44, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h47 | h47
                      · linarith only [h43, h47, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h47, h6, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h30, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h51 | h51
          · linarith only [h51, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 5 (by decide) (by decide) with h54 | h54
              · rcases m.htr 0 2 3 (by decide) (by decide) with h55 | h55
                · rcases m.htr 0 2 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h58, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h51, h58, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
                      · linarith only [h57, h61, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h51, h56, h61, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h5, h53, h56, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h55, h65, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h5, h65, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h54, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h69 | h69
              · rcases m.htr 0 2 3 (by decide) (by decide) with h70 | h70
                · rcases m.htr 0 2 5 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
                      · linarith only [h73, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h51, h71, h73, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
                      · linarith only [h72, h76, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h51, h76, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h5, h69, h71, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h80 | h80
                  · linarith only [h70, h80, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h5, h80, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h69, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h85 | h85
    · rcases p0_3 (m.d 1 5) (by simp) with h86 | h86
      · rcases p0_3 (m.d 2 5) (by simp) with h87 | h87
        · linarith only [h87, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h89 | h89
          · linarith only [h89, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h91 | h91
            · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
              · linarith only [h86, h92, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h94 | h94
                · rcases m.htr 0 2 5 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h97 | h97
                      · linarith only [h97, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h89, h97, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h100 | h100
                      · linarith only [h100, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h100, h89, h95, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h95, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h94, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h104, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
              · linarith only [h107, h86, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 2 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
                      · linarith only [h112, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h112, h89, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
                      · linarith only [h111, h115, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h110, h115, h89, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h110, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h119 | h119
                  · linarith only [h109, h119, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h119, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h122 | h122
        · linarith only [h122, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h124 | h124
          · linarith only [h124, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · rcases m.htr 0 1 5 (by decide) (by decide) with h127 | h127
              · rcases m.htr 0 2 3 (by decide) (by decide) with h128 | h128
                · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h131, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h124, h127, h131, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
                      · linarith only [h134, h86, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h124, h127, h134, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h129, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h138 | h138
                  · linarith only [h128, h138, h86, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h138, hlam, p0_0]
              · linarith only [h127, h86, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h142 | h142
              · rcases m.htr 0 2 3 (by decide) (by decide) with h143 | h143
                · rcases m.htr 0 2 5 (by decide) (by decide) with h144 | h144
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h146 | h146
                      · linarith only [h146, h86, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h124, h142, h146, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
                      · linarith only [h145, h149, h86, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h124, h144, h149, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h144, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h143, h153, h86, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo2]
                  · linarith only [h153, hlam, p0_0]
              · linarith only [h142, h86, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h85, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h158 | h158
    · rcases p0_3 (m.d 1 5) (by simp) with h159 | h159
      · rcases p0_3 (m.d 2 5) (by simp) with h160 | h160
        · rcases p0_3 (m.d 3 5) (by simp) with h161 | h161
          · linarith only [h161, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h163 | h163
            · rcases m.htr 0 1 5 (by decide) (by decide) with h164 | h164
              · linarith only [h159, h164, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h166 | h166
                · rcases m.htr 0 2 5 (by decide) (by decide) with h167 | h167
                  · linarith only [h160, h167, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
                      · linarith only [h170, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h170, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h169, h173, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h173, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h160, h176, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
                      · linarith only [h179, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h179, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h182 | h182
                      · linarith only [h178, h182, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h182, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h185 | h185
              · linarith only [h159, h185, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h187 | h187
                · rcases m.htr 0 2 5 (by decide) (by decide) with h188 | h188
                  · linarith only [h160, h188, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h190 | h190
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h191 | h191
                      · linarith only [h191, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h191, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h194 | h194
                      · linarith only [h190, h194, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h194, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h160, h197, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
                      · linarith only [h200, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h200, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h203 | h203
                      · linarith only [h199, h203, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h206 | h206
          · linarith only [h206, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h208 | h208
            · rcases m.htr 0 1 5 (by decide) (by decide) with h209 | h209
              · linarith only [h159, h209, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h211 | h211
                · rcases m.htr 0 2 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h214 | h214
                      · linarith only [h214, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h214, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h217 | h217
                      · linarith only [h213, h217, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h217, hlam, p0_0]
                  · linarith only [h160, h212, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h211, h221, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h160, h221, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h224 | h224
              · linarith only [h159, h224, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h226 | h226
                · rcases m.htr 0 2 5 (by decide) (by decide) with h227 | h227
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
                      · linarith only [h160, h229, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h229, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h232 | h232
                      · linarith only [h160, h228, h232, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h232, hlam, p0_0]
                  · linarith only [h160, h227, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h226, h236, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h160, h236, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 2 5) (by simp) with h239 | h239
        · rcases p0_3 (m.d 3 5) (by simp) with h240 | h240
          · linarith only [h240, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h242 | h242
            · rcases m.htr 0 1 5 (by decide) (by decide) with h243 | h243
              · rcases m.htr 0 2 3 (by decide) (by decide) with h244 | h244
                · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
                  · linarith only [h239, h245, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h247 | h247
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h248 | h248
                      · linarith only [h159, h248, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h248, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h251 | h251
                      · linarith only [h159, h247, h251, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h251, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
                  · linarith only [h239, h254, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
                      · linarith only [h159, h257, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h257, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h260 | h260
                      · linarith only [h159, h256, h260, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h260, hlam, p0_0]
              · linarith only [h159, h243, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
              · rcases m.htr 0 2 3 (by decide) (by decide) with h265 | h265
                · rcases m.htr 0 2 5 (by decide) (by decide) with h266 | h266
                  · linarith only [h239, h266, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h269 | h269
                      · linarith only [h159, h269, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h269, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
                      · linarith only [h159, h268, h272, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h272, hlam, p0_0]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
                  · linarith only [h239, h275, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h278 | h278
                      · linarith only [h159, h278, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h278, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h281 | h281
                      · linarith only [h159, h277, h281, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h281, hlam, p0_0]
              · linarith only [h159, h264, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h285 | h285
          · linarith only [h285, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · rcases m.htr 0 1 5 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 2 3 (by decide) (by decide) with h289 | h289
                · rcases m.htr 0 2 5 (by decide) (by decide) with h290 | h290
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h292 | h292
                      · linarith only [h159, h292, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h292, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h295 | h295
                      · linarith only [h159, h291, h295, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h295, hlam, p0_0]
                  · linarith only [h239, h288, h290, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h299 | h299
                  · linarith only [h159, h289, h299, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h239, h299, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h159, h287, h288, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h303 | h303
              · rcases m.htr 0 2 3 (by decide) (by decide) with h304 | h304
                · rcases m.htr 0 2 5 (by decide) (by decide) with h305 | h305
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h307 | h307
                      · linarith only [h159, h307, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h307, hlam, p0_0]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h310 | h310
                      · linarith only [h159, h306, h310, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h310, hlam, p0_0]
                  · linarith only [h239, h303, h305, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h314 | h314
                  · linarith only [h159, h304, h314, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h239, h303, h314, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h159, h303, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h158, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h319 | h319
    · rcases p0_3 (m.d 1 5) (by simp) with h320 | h320
      · rcases p0_3 (m.d 2 5) (by simp) with h321 | h321
        · rcases p0_3 (m.d 3 5) (by simp) with h322 | h322
          · linarith only [h322, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h324 | h324
            · linarith only [h324, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h326 | h326
              · linarith only [h320, h326, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h328 | h328
                · rcases m.htr 0 2 5 (by decide) (by decide) with h329 | h329
                  · linarith only [h321, h329, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h332 | h332
                      · linarith only [h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h322, h332, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h335 | h335
                      · linarith only [h331, h335, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h322, h335, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h338 | h338
                  · linarith only [h321, h338, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h340 | h340
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h341 | h341
                      · linarith only [h341, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h322, h341, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h344 | h344
                      · linarith only [h340, h344, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h322, h344, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h347 | h347
          · linarith only [h321, h347, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h349 | h349
            · linarith only [h349, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h351 | h351
              · linarith only [h320, h351, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h353 | h353
                · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
                      · linarith only [h321, h356, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h347, h356, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h359 | h359
                      · linarith only [h355, h359, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h347, h354, h359, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h321, h351, h354, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h363 | h363
                  · linarith only [h347, h353, h363, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h321, h363, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 2 5) (by simp) with h366 | h366
        · rcases p0_3 (m.d 3 5) (by simp) with h367 | h367
          · linarith only [h320, h367, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h369 | h369
            · linarith only [h369, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h371 | h371
              · rcases m.htr 0 2 3 (by decide) (by decide) with h372 | h372
                · rcases m.htr 0 2 5 (by decide) (by decide) with h373 | h373
                  · linarith only [h366, h373, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h375 | h375
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h376 | h376
                      · linarith only [h320, h376, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h367, h371, h376, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h379 | h379
                      · linarith only [h320, h375, h379, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h367, h379, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h382 | h382
                  · linarith only [h366, h382, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h384 | h384
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h385 | h385
                      · linarith only [h367, h385, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h367, h385, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h388 | h388
                      · linarith only [h384, h388, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h367, h388, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h320, h366, h371, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h392 | h392
          · linarith only [h320, h392, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h394 | h394
            · linarith only [h394, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h396 | h396
              · rcases m.htr 0 2 3 (by decide) (by decide) with h397 | h397
                · rcases m.htr 0 2 5 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h399 | h399
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
                      · linarith only [h320, h400, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h392, h396, h400, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
                      · linarith only [h320, h399, h403, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h392, h396, h403, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h366, h396, h398, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h407 | h407
                  · linarith only [h320, h397, h407, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h366, h407, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h320, h396, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h319, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h412 | h412
    · linarith only [h412, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h414 | h414
      · rcases p0_3 (m.d 2 5) (by simp) with h415 | h415
        · rcases p0_3 (m.d 3 5) (by simp) with h416 | h416
          · linarith only [h416, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h418 | h418
            · rcases m.htr 0 1 5 (by decide) (by decide) with h419 | h419
              · linarith only [h419, hlam, p0_0]
              · linarith only [h419, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h422 | h422
              · linarith only [h422, hlam, p0_0]
              · linarith only [h415, h422, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h425 | h425
          · linarith only [h425, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h427 | h427
            · rcases m.htr 0 1 5 (by decide) (by decide) with h428 | h428
              · linarith only [h428, hlam, p0_0]
              · linarith only [h428, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h431 | h431
              · linarith only [h431, hlam, p0_0]
              · linarith only [h431, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h414, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h436 | h436
    · rcases p0_3 (m.d 1 5) (by simp) with h437 | h437
      · rcases p0_3 (m.d 2 5) (by simp) with h438 | h438
        · linarith only [h438, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h440 | h440
          · linarith only [h440, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h442 | h442
            · rcases m.htr 0 1 5 (by decide) (by decide) with h443 | h443
              · linarith only [h443, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h436, h443, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h446 | h446
              · linarith only [h446, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h436, h446, hlam]
      · linarith only [h437, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h450 | h450
      · rcases p0_3 (m.d 2 5) (by simp) with h451 | h451
        · linarith only [h451, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h453 | h453
          · linarith only [h453, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h455 | h455
            · rcases m.htr 0 1 5 (by decide) (by decide) with h456 | h456
              · linarith only [h456, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h436, h456, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h459 | h459
              · linarith only [h436, h459, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h436, h459, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h450, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h463 | h463
    · rcases p0_3 (m.d 1 5) (by simp) with h464 | h464
      · rcases p0_3 (m.d 2 5) (by simp) with h465 | h465
        · rcases p0_3 (m.d 3 5) (by simp) with h466 | h466
          · linarith only [h466, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · rcases m.htr 0 1 5 (by decide) (by decide) with h469 | h469
              · linarith only [h469, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h469, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h472 | h472
              · linarith only [h472, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h472, hlam]
        · rcases p0_3 (m.d 3 5) (by simp) with h475 | h475
          · linarith only [h475, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h477 | h477
            · rcases m.htr 0 1 5 (by decide) (by decide) with h478 | h478
              · linarith only [h478, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h478, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h481 | h481
              · linarith only [h481, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h481, hlam]
      · linarith only [h464, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h485 | h485
      · rcases p0_3 (m.d 2 5) (by simp) with h486 | h486
        · rcases p0_3 (m.d 3 5) (by simp) with h487 | h487
          · linarith only [h487, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h489 | h489
            · rcases m.htr 0 1 5 (by decide) (by decide) with h490 | h490
              · linarith only [h490, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h490, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h493 | h493
              · linarith only [h463, h493, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h493, hc01, hc15, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h496 | h496
          · linarith only [h496, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h498 | h498
            · rcases m.htr 0 1 5 (by decide) (by decide) with h499 | h499
              · linarith only [h463, h499, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h499, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h502 | h502
              · linarith only [h463, h502, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h463, h502, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h485, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h506 | h506
    · rcases p0_3 (m.d 1 5) (by simp) with h507 | h507
      · rcases p0_3 (m.d 2 5) (by simp) with h508 | h508
        · rcases p0_3 (m.d 3 5) (by simp) with h509 | h509
          · linarith only [h509, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h511 | h511
            · linarith only [h511, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h513 | h513
              · linarith only [h513, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h506, h513, hlam]
        · rcases p0_3 (m.d 3 5) (by simp) with h516 | h516
          · linarith only [h516, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h518 | h518
            · linarith only [h518, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h520 | h520
              · linarith only [h520, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h506, h520, hlam]
      · linarith only [h507, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h524 | h524
      · rcases p0_3 (m.d 2 5) (by simp) with h525 | h525
        · rcases p0_3 (m.d 3 5) (by simp) with h526 | h526
          · linarith only [h526, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h528 | h528
            · linarith only [h528, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h530 | h530
              · linarith only [h530, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h506, h530, hc01, hc15, hlam, hphi, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h533 | h533
          · linarith only [h506, h533, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h535 | h535
            · linarith only [h535, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h537 | h537
              · linarith only [h506, h537, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h506, h537, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h524, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h541 | h541
    · linarith only [h541, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h543 | h543
      · rcases p0_3 (m.d 2 5) (by simp) with h544 | h544
        · rcases p0_3 (m.d 3 5) (by simp) with h545 | h545
          · linarith only [h545, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h547 | h547
            · rcases m.htr 0 1 5 (by decide) (by decide) with h548 | h548
              · linarith only [h543, h548, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h543, h548, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h551 | h551
              · linarith only [h543, h551, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h543, h551, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h544, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h555 | h555
        · rcases p0_3 (m.d 3 5) (by simp) with h556 | h556
          · linarith only [h556, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h558 | h558
            · rcases m.htr 0 1 5 (by decide) (by decide) with h559 | h559
              · rcases m.htr 0 2 3 (by decide) (by decide) with h560 | h560
                · rcases m.htr 0 2 5 (by decide) (by decide) with h561 | h561
                  · linarith only [h561, hlam, p0_0]
                  · linarith only [h558, h561, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h564 | h564
                  · linarith only [h564, hlam, p0_0]
                  · linarith only [h558, h564, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h543, h559, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h568 | h568
              · rcases m.htr 0 2 3 (by decide) (by decide) with h569 | h569
                · rcases m.htr 0 2 5 (by decide) (by decide) with h570 | h570
                  · linarith only [h570, hlam, p0_0]
                  · linarith only [h569, h570, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h573 | h573
                  · linarith only [h573, hlam, p0_0]
                  · linarith only [h573, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h543, h568, hlam]
        · linarith only [h555, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h578 | h578
    · rcases p0_3 (m.d 1 5) (by simp) with h579 | h579
      · linarith only [h579, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h581 | h581
        · rcases p0_3 (m.d 3 5) (by simp) with h582 | h582
          · linarith only [h582, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h584 | h584
            · rcases m.htr 0 1 5 (by decide) (by decide) with h585 | h585
              · rcases m.htr 0 2 3 (by decide) (by decide) with h586 | h586
                · rcases m.htr 0 2 5 (by decide) (by decide) with h587 | h587
                  · linarith only [h587, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h578, h587, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h590 | h590
                  · linarith only [h590, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h578, h590, hlam]
              · linarith only [h585, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h594 | h594
              · rcases m.htr 0 2 3 (by decide) (by decide) with h595 | h595
                · rcases m.htr 0 2 5 (by decide) (by decide) with h596 | h596
                  · linarith only [h596, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h578, h596, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h599 | h599
                  · linarith only [h599, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h578, h599, hlam]
              · linarith only [h594, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h581, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h604 | h604
      · linarith only [h604, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h606 | h606
        · rcases p0_3 (m.d 3 5) (by simp) with h607 | h607
          · linarith only [h578, h607, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h609 | h609
            · rcases m.htr 0 1 5 (by decide) (by decide) with h610 | h610
              · linarith only [h578, h610, hlam]
              · linarith only [h610, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h613 | h613
              · linarith only [h578, h613, hlam]
              · linarith only [h613, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h606, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h618 | h618
    · rcases p0_3 (m.d 1 5) (by simp) with h619 | h619
      · rcases p0_3 (m.d 2 5) (by simp) with h620 | h620
        · rcases p0_3 (m.d 3 5) (by simp) with h621 | h621
          · linarith only [h621, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h623 | h623
            · rcases m.htr 0 1 5 (by decide) (by decide) with h624 | h624
              · linarith only [h619, h624, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h626 | h626
                · rcases m.htr 0 2 5 (by decide) (by decide) with h627 | h627
                  · linarith only [h627, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h627, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h630 | h630
                  · linarith only [h630, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h630, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h633 | h633
              · linarith only [h619, h633, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h635 | h635
                · rcases m.htr 0 2 5 (by decide) (by decide) with h636 | h636
                  · linarith only [h636, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h636, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h639 | h639
                  · linarith only [h639, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h639, hlam]
        · linarith only [h620, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h643 | h643
        · rcases p0_3 (m.d 3 5) (by simp) with h644 | h644
          · linarith only [h644, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h646 | h646
            · rcases m.htr 0 1 5 (by decide) (by decide) with h647 | h647
              · rcases m.htr 0 2 3 (by decide) (by decide) with h648 | h648
                · rcases m.htr 0 2 5 (by decide) (by decide) with h649 | h649
                  · linarith only [h649, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h649, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h652 | h652
                  · linarith only [h652, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h652, hlam]
              · linarith only [h619, h647, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h656 | h656
              · rcases m.htr 0 2 3 (by decide) (by decide) with h657 | h657
                · rcases m.htr 0 2 5 (by decide) (by decide) with h658 | h658
                  · linarith only [h619, h658, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h658, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h661 | h661
                  · linarith only [h619, h661, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h661, hlam]
              · linarith only [h619, h656, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h643, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h666 | h666
      · rcases p0_3 (m.d 2 5) (by simp) with h667 | h667
        · rcases p0_3 (m.d 3 5) (by simp) with h668 | h668
          · linarith only [h668, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h670 | h670
            · rcases m.htr 0 1 5 (by decide) (by decide) with h671 | h671
              · linarith only [h618, h666, h671, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h618, h666, h671, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h674 | h674
              · linarith only [h618, h666, h674, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h618, h666, h674, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h667, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h678 | h678
        · rcases p0_3 (m.d 3 5) (by simp) with h679 | h679
          · linarith only [h679, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h681 | h681
            · rcases m.htr 0 1 5 (by decide) (by decide) with h682 | h682
              · rcases m.htr 0 2 3 (by decide) (by decide) with h683 | h683
                · rcases m.htr 0 2 5 (by decide) (by decide) with h684 | h684
                  · linarith only [h618, h682, h684, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h681, h684, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h687 | h687
                  · linarith only [h618, h682, h687, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h681, h687, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h666, h681, h682, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h691 | h691
              · rcases m.htr 0 2 3 (by decide) (by decide) with h692 | h692
                · rcases m.htr 0 2 5 (by decide) (by decide) with h693 | h693
                  · linarith only [h618, h691, h693, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h692, h693, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h696 | h696
                  · linarith only [h618, h696, hc02, hc05, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h618, h696, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h666, h691, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h678, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h701 | h701
    · rcases p0_3 (m.d 1 5) (by simp) with h702 | h702
      · rcases p0_3 (m.d 2 5) (by simp) with h703 | h703
        · rcases p0_3 (m.d 3 5) (by simp) with h704 | h704
          · linarith only [h704, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h706 | h706
            · linarith only [h706, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h708 | h708
              · linarith only [h702, h708, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h710 | h710
                · rcases m.htr 0 2 5 (by decide) (by decide) with h711 | h711
                  · linarith only [h711, hc02, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h701, h711, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h714 | h714
                  · linarith only [h714, hc02, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h701, h714, hlam]
        · linarith only [h703, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h718 | h718
        · rcases p0_3 (m.d 3 5) (by simp) with h719 | h719
          · linarith only [h719, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h721 | h721
            · linarith only [h721, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h723 | h723
              · rcases m.htr 0 2 3 (by decide) (by decide) with h724 | h724
                · rcases m.htr 0 2 5 (by decide) (by decide) with h725 | h725
                  · linarith only [h725, hc02, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h701, h725, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h728 | h728
                  · linarith only [h728, hc02, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h701, h728, hlam]
              · linarith only [h702, h723, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h718, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h733 | h733
      · rcases p0_3 (m.d 2 5) (by simp) with h734 | h734
        · rcases p0_3 (m.d 3 5) (by simp) with h735 | h735
          · linarith only [h701, h735, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h737 | h737
            · linarith only [h737, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h739 | h739
              · linarith only [h701, h733, h739, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h701, h733, h739, hc01, hc15, hlam, hphi, p0_1]
        · linarith only [h734, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h743 | h743
        · rcases p0_3 (m.d 3 5) (by simp) with h744 | h744
          · linarith only [h701, h744, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h746 | h746
            · linarith only [h746, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h748 | h748
              · rcases m.htr 0 2 3 (by decide) (by decide) with h749 | h749
                · rcases m.htr 0 2 5 (by decide) (by decide) with h750 | h750
                  · linarith only [h701, h748, h750, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h701, h749, h750, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h753 | h753
                  · linarith only [h701, h753, hc02, hc05, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h701, h753, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h733, h748, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h743, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h763 | h763
    · linarith only [h763, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h765 | h765
      · rcases p0_3 (m.d 2 5) (by simp) with h766 | h766
        · rcases p0_3 (m.d 3 5) (by simp) with h767 | h767
          · linarith only [h767, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h769 | h769
            · rcases m.htr 0 1 5 (by decide) (by decide) with h770 | h770
              · linarith only [h765, h770, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h765, h770, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h769, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h774 | h774
          · linarith only [h774, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h776 | h776
            · rcases m.htr 0 1 5 (by decide) (by decide) with h777 | h777
              · linarith only [h765, h777, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h765, h777, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h776, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h781 | h781
        · rcases p0_3 (m.d 3 5) (by simp) with h782 | h782
          · linarith only [h782, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h784 | h784
            · rcases m.htr 0 1 5 (by decide) (by decide) with h785 | h785
              · rcases m.htr 0 2 3 (by decide) (by decide) with h786 | h786
                · rcases m.htr 0 2 5 (by decide) (by decide) with h787 | h787
                  · linarith only [h781, h785, h787, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h786, h787, hc23, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h790 | h790
                  · linarith only [h781, h785, h790, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h790, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h765, h785, hlam]
            · linarith only [h784, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h795 | h795
          · linarith only [h795, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h797 | h797
            · rcases m.htr 0 1 5 (by decide) (by decide) with h798 | h798
              · rcases m.htr 0 2 3 (by decide) (by decide) with h799 | h799
                · rcases m.htr 0 2 5 (by decide) (by decide) with h800 | h800
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h801 | h801
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h803 | h803
                        · linarith only [h803, hlam, p0_0]
                        · linarith only [h803, hc04, hc45, hlam, hphi, p0_1]
                      · linarith only [h795, h802, hlam]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h807 | h807
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h808 | h808
                        · linarith only [h808, hlam, p0_0]
                        · linarith only [h801, h808, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · linarith only [h795, h807, hlam]
                  · linarith only [h781, h800, hlam]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h813 | h813
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h814 | h814
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h815 | h815
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h816 | h816
                        · linarith only [h816, hlam, p0_0]
                        · linarith only [h814, h816, hc34, hc45, hlam, hphi, p0_1]
                      · linarith only [h795, h815, hlam]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h820 | h820
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h821 | h821
                        · linarith only [h821, hlam, p0_0]
                        · linarith only [h814, h821, hc03, hc45, hlam, hphi, ht34, p0_1]
                      · linarith only [h795, h820, hlam]
                  · linarith only [h781, h813, hlam]
              · linarith only [h765, h798, hlam]
            · linarith only [h797, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h828 | h828
    · rcases p0_3 (m.d 1 5) (by simp) with h829 | h829
      · linarith only [h829, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h831 | h831
        · rcases p0_3 (m.d 3 5) (by simp) with h832 | h832
          · linarith only [h832, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h834 | h834
            · rcases m.htr 0 1 5 (by decide) (by decide) with h835 | h835
              · rcases m.htr 0 2 3 (by decide) (by decide) with h836 | h836
                · rcases m.htr 0 2 5 (by decide) (by decide) with h837 | h837
                  · linarith only [h831, h837, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h839 | h839
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h840 | h840
                      · linarith only [h828, h840, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h828, h832, h835, h840, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h843 | h843
                      · linarith only [h828, h839, h843, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h828, h832, h843, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h846 | h846
                  · linarith only [h831, h846, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h848 | h848
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h849 | h849
                      · linarith only [h828, h836, h849, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo2]
                      · linarith only [h828, h832, h849, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h852 | h852
                      · linarith only [h828, h848, h852, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h828, h832, h852, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h835, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h834, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h857 | h857
          · linarith only [h857, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h859 | h859
            · rcases m.htr 0 1 5 (by decide) (by decide) with h860 | h860
              · rcases m.htr 0 2 3 (by decide) (by decide) with h861 | h861
                · rcases m.htr 0 2 5 (by decide) (by decide) with h862 | h862
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h863 | h863
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h864 | h864
                      · linarith only [h828, h864, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h828, h857, h860, h864, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h867 | h867
                      · linarith only [h828, h863, h867, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h828, h857, h860, h867, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h831, h862, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h871 | h871
                  · linarith only [h828, h861, h871, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h828, h831, h871, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h860, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h859, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h876 | h876
      · linarith only [h876, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h878 | h878
        · rcases p0_3 (m.d 3 5) (by simp) with h879 | h879
          · linarith only [h828, h879, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h881 | h881
            · rcases m.htr 0 1 5 (by decide) (by decide) with h882 | h882
              · linarith only [h828, h882, hlam]
              · linarith only [h878, h882, hc01, hc25, hlam, hphi, ht12, p0_1]
            · linarith only [h881, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h886 | h886
          · linarith only [h886, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h888 | h888
            · rcases m.htr 0 1 5 (by decide) (by decide) with h889 | h889
              · linarith only [h828, h889, hlam]
              · linarith only [h889, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h888, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h893 | h893
    · rcases p0_3 (m.d 1 5) (by simp) with h894 | h894
      · rcases p0_3 (m.d 2 5) (by simp) with h895 | h895
        · linarith only [h895, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h897 | h897
          · linarith only [h897, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h899 | h899
            · rcases m.htr 0 1 5 (by decide) (by decide) with h900 | h900
              · linarith only [h894, h900, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h902 | h902
                · rcases m.htr 0 2 5 (by decide) (by decide) with h903 | h903
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h904 | h904
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h905 | h905
                      · linarith only [h893, h905, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h893, h897, h905, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h908 | h908
                      · linarith only [h893, h904, h908, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h893, h897, h903, h908, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h903, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h912 | h912
                  · linarith only [h893, h902, h912, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h893, h912, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h899, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h916 | h916
        · linarith only [h916, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h918 | h918
          · linarith only [h894, h918, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h920 | h920
            · rcases m.htr 0 1 5 (by decide) (by decide) with h921 | h921
              · rcases m.htr 0 2 3 (by decide) (by decide) with h922 | h922
                · rcases m.htr 0 2 5 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h924 | h924
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h925 | h925
                      · linarith only [h893, h894, h925, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h893, h918, h923, h925, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h928 | h928
                      · linarith only [h893, h924, h928, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h893, h918, h928, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h923, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h932 | h932
                  · linarith only [h893, h922, h932, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h893, h932, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h894, h921, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h920, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h937 | h937
      · rcases p0_3 (m.d 2 5) (by simp) with h938 | h938
        · linarith only [h938, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h940 | h940
          · linarith only [h893, h940, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h942 | h942
            · rcases m.htr 0 1 5 (by decide) (by decide) with h943 | h943
              · linarith only [h893, h937, h943, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h893, h937, h943, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h942, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h947 | h947
        · linarith only [h947, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h949 | h949
          · linarith only [h893, h949, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
          · rcases p0_3 (m.d 4 5) (by simp) with h951 | h951
            · rcases m.htr 0 1 5 (by decide) (by decide) with h952 | h952
              · rcases m.htr 0 2 3 (by decide) (by decide) with h953 | h953
                · rcases m.htr 0 2 5 (by decide) (by decide) with h954 | h954
                  · linarith only [h893, h954, hlam]
                  · linarith only [h953, h954, hc23, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h957 | h957
                  · linarith only [h893, h957, hlam]
                  · linarith only [h957, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h937, h952, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h951, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h962 | h962
    · rcases p0_3 (m.d 1 5) (by simp) with h963 | h963
      · rcases p0_3 (m.d 2 5) (by simp) with h964 | h964
        · rcases p0_3 (m.d 3 5) (by simp) with h965 | h965
          · linarith only [h965, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h967 | h967
            · rcases m.htr 0 1 5 (by decide) (by decide) with h968 | h968
              · linarith only [h963, h968, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h970 | h970
                · rcases m.htr 0 2 5 (by decide) (by decide) with h971 | h971
                  · linarith only [h964, h971, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h973 | h973
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h974 | h974
                      · linarith only [h962, h974, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h962, h974, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h977 | h977
                      · linarith only [h962, h973, h977, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h962, h977, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h980 | h980
                  · linarith only [h964, h980, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h983 | h983
                      · linarith only [h962, h970, h983, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo2]
                      · linarith only [h962, h983, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h986 | h986
                      · linarith only [h962, h982, h986, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h962, h986, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h967, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h990 | h990
          · linarith only [h990, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h992 | h992
            · rcases m.htr 0 1 5 (by decide) (by decide) with h993 | h993
              · linarith only [h963, h964, h993, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h995 | h995
                · rcases m.htr 0 2 5 (by decide) (by decide) with h996 | h996
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h997 | h997
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h998 | h998
                      · linarith only [h962, h964, h998, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h962, h996, h998, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1001 | h1001
                      · linarith only [h1001, h962, h964, h997, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h1001, h962, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h964, h996, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1005 | h1005
                  · linarith only [h1005, h962, h995, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h1005, h962, h964, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h992, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1009 | h1009
        · rcases p0_3 (m.d 3 5) (by simp) with h1010 | h1010
          · linarith only [h1010, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1012 | h1012
            · rcases m.htr 0 1 5 (by decide) (by decide) with h1013 | h1013
              · rcases m.htr 0 2 3 (by decide) (by decide) with h1014 | h1014
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1015 | h1015
                  · linarith only [h1009, h1015, h963, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h1017 | h1017
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1018 | h1018
                      · linarith only [h1018, h962, h963, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h1018, h962, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1021 | h1021
                      · linarith only [h1017, h1021, h962, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h1021, h962, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1024 | h1024
                  · linarith only [h1009, h1024, hc02, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h1026 | h1026
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1027 | h1027
                      · linarith only [h1014, h1027, h962, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo2]
                      · linarith only [h1027, h962, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1030 | h1030
                      · linarith only [h1026, h1030, h962, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h1030, h962, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h1013, h963, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1012, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1035 | h1035
          · linarith only [h1035, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1037 | h1037
            · rcases m.htr 0 1 5 (by decide) (by decide) with h1038 | h1038
              · rcases m.htr 0 2 3 (by decide) (by decide) with h1039 | h1039
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1040 | h1040
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h1041 | h1041
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1042 | h1042
                      · linarith only [h1042, h962, h963, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                      · linarith only [h1040, h1042, h962, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1045 | h1045
                      · linarith only [h1009, h1041, h1045, h962, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
                      · linarith only [h1045, h962, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h1009, h1040, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1049 | h1049
                  · linarith only [h1039, h1049, h962, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                  · linarith only [h1009, h1049, h962, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h1038, h963, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1037, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h1054 | h1054
      · rcases p0_3 (m.d 2 5) (by simp) with h1055 | h1055
        · rcases p0_3 (m.d 3 5) (by simp) with h1056 | h1056
          · linarith only [h1056, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1058 | h1058
            · rcases m.htr 0 1 5 (by decide) (by decide) with h1059 | h1059
              · linarith only [h1054, h1059, h962, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h1054, h1059, h962, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h1058, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1063 | h1063
          · linarith only [h1063, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1065 | h1065
            · rcases m.htr 0 1 5 (by decide) (by decide) with h1066 | h1066
              · linarith only [h1054, h1066, h962, hc01, hc05, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h1054, h1066, h962, hc01, hc15, hlam, hphi, p0_1]
            · linarith only [h1065, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1070 | h1070
        · rcases p0_3 (m.d 3 5) (by simp) with h1071 | h1071
          · linarith only [h1071, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1073 | h1073
            · rcases m.htr 0 1 5 (by decide) (by decide) with h1074 | h1074
              · rcases m.htr 0 2 3 (by decide) (by decide) with h1075 | h1075
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1076 | h1076
                  · linarith only [h1070, h1074, h1076, h962, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h1076, h962, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1079 | h1079
                  · linarith only [h1070, h1074, h1079, h962, hc02, hc15, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h1079, h962, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h1054, h1074, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1073, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1084 | h1084
          · linarith only [h1084, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1086 | h1086
            · rcases m.htr 0 1 5 (by decide) (by decide) with h1087 | h1087
              · rcases m.htr 0 2 3 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1089 | h1089
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h1090 | h1090
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1091 | h1091
                      · linarith only [h1091, h962, hlam]
                      · linarith only [h1091, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1094 | h1094
                      · linarith only [h1094, h962, hlam]
                      · linarith only [h1088, h1094, hc23, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h1070, h1088, h1089, hc23, hc45, hlam, hphi, ht34, p0_1]
                · rcases m.htr 0 2 5 (by decide) (by decide) with h1098 | h1098
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h1099 | h1099
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1100 | h1100
                      · linarith only [h1100, h962, hlam]
                      · linarith only [h1099, h1100, hc34, hc45, hlam, hphi, p0_1]
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1103 | h1103
                      · linarith only [h1103, h962, hlam]
                      · linarith only [h1103, hc03, hc45, hlam, hphi, ht34, p0_1]
                  · linarith only [h1070, h1098, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h1054, h1087, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1086, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
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
        · linarith only [h5, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
            · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h10 | h10 | h10 | h10 | h10
              · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
                · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                    · linarith only [h13, h7, hlam]
                    · linarith only [h11, h13, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h11, h12, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h11, hlam, p0_0]
              · linarith only [h10, hc01, hlam, p0_1]
              · linarith only [h10, h5, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 1 3 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
                    · linarith only [h22, h7, hlam]
                    · linarith only [h20, h22, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h20, h21, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h20, hlam, p0_0]
              · linarith only [h10, h8, hc01, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h28 | h28
            · linarith only [h28, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h30 | h30 | h30 | h30 | h30
              · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
                · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h35 | h35
                        · linarith only [h35, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · linarith only [h35, h5, hlam]
                      · linarith only [h30, h34, hc15, hlam, ht01]
                    · linarith only [h31, h33, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h31, h32, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h31, hlam, p0_0]
              · linarith only [h30, hc01, hlam, p0_1]
              · linarith only [h30, hlam, ht01, ht12, ht23, u3elo0]
              · linarith only [h30, h7, hc01, hlam, p0_1]
              · linarith only [h28, h30, hc01, hlam, p0_1]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h47 | h47
    · rcases p0_3 (m.d 0 2) (by simp) with h48 | h48
      · rcases p0_3 (m.d 0 3) (by simp) with h49 | h49
        · linarith only [h49, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h51 | h51
          · rcases p0_3 (m.d 0 5) (by simp) with h52 | h52
            · linarith only [h52, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h54 | h54 | h54 | h54 | h54
              · rcases m.htr 0 1 2 (by decide) (by decide) with h55 | h55
                · linarith only [h48, h55, hlam]
                · linarith only [h55, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
                · linarith only [h48, h58, hlam]
                · linarith only [h58, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h54, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
                · linarith only [h48, h62, hlam]
                · linarith only [h62, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h52, h54, hc01, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · linarith only [h66, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h68 | h68 | h68 | h68 | h68
              · rcases m.htr 0 1 2 (by decide) (by decide) with h69 | h69
                · linarith only [h48, h69, hlam]
                · linarith only [h69, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h72 | h72
                · linarith only [h48, h72, hlam]
                · linarith only [h72, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h68, hc01, hlam, p0_1]
              · linarith only [h51, h68, hc01, hlam, p0_1]
              · linarith only [h66, h68, hc01, hlam, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h78 | h78
        · linarith only [h78, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h80 | h80
          · rcases p0_3 (m.d 0 5) (by simp) with h81 | h81
            · linarith only [h48, h81, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h83 | h83 | h83 | h83 | h83
              · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
                · rcases m.htr 0 1 3 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h86 | h86
                    · linarith only [h80, h86, hlam]
                    · linarith only [h48, h84, h86, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h85, hlam, p0_0]
                · linarith only [h83, h84, hc12, hlam, ht01]
              · linarith only [h48, h83, hc01, hlam, p0_1]
              · linarith only [h83, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h93 | h93
                · rcases m.htr 0 1 3 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h95 | h95
                    · linarith only [h80, h95, hlam]
                    · linarith only [h48, h93, h95, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h94, hlam, p0_0]
                · linarith only [h48, h93, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h81, h83, hc01, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h101 | h101
            · linarith only [h101, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h103 | h103 | h103 | h103 | h103
              · rcases m.htr 0 1 2 (by decide) (by decide) with h104 | h104
                · rcases m.htr 0 1 3 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h108 | h108
                        · linarith only [h108, h48, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h110 | h110
                          · linarith only [h108, h110, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h112 | h112
                            · linarith only [h108, h112, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
                              · linarith only [h114, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h114, h80, hlam]
                      · linarith only [h103, h107, hc15, hlam, ht01]
                    · linarith only [h103, h106, hc14, hlam, ht01]
                  · linarith only [h105, hlam, p0_0]
                · linarith only [h104, h48, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h103, h48, hc01, hlam, p0_1]
              · linarith only [h103, hc01, hlam, p0_1]
              · linarith only [h103, h80, hc01, hlam, p0_1]
              · linarith only [h103, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
    · linarith only [h47, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h126 | h126
    · rcases p0_3 (m.d 0 2) (by simp) with h127 | h127
      · rcases p0_3 (m.d 0 3) (by simp) with h128 | h128
        · linarith only [h128, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h130 | h130
          · linarith only [h130, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h132 | h132
            · linarith only [h128, h132, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h134 | h134 | h134 | h134 | h134
              · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
                · linarith only [h127, h135, hlam]
                · linarith only [h128, h135, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h138 | h138
                · linarith only [h127, h138, hlam]
                · linarith only [h128, h138, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h128, h134, hc01, hlam, p0_1]
              · linarith only [h134, hc01, hlam, p0_1]
              · linarith only [h132, h134, hc01, hlam, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h144 | h144
        · linarith only [h127, h144, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
          · linarith only [h146, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h148 | h148
            · linarith only [h127, h148, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h150 | h150 | h150 | h150 | h150
              · rcases m.htr 0 1 2 (by decide) (by decide) with h151 | h151
                · rcases m.htr 0 1 3 (by decide) (by decide) with h152 | h152
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h154 | h154
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h155 | h155
                        · linarith only [h127, h155, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h157 | h157
                          · linarith only [h127, h157, hlam]
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
                            · linarith only [h144, h155, h159, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
                              · linarith only [h144, h161, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                                · linarith only [h161, h163, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                                  · linarith only [h165, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                  · linarith only [h148, h165, hlam]
                      · linarith only [h150, h154, hc15, hlam, ht01]
                    · linarith only [h153, hlam, p0_0]
                  · linarith only [h150, h152, hc13, hlam, ht01]
                · linarith only [h127, h151, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h127, h150, hc01, hlam, p0_1]
              · linarith only [h150, hlam, ht01, ht12, ht23, u3elo0]
              · linarith only [h150, hc01, hlam, p0_1]
              · linarith only [h150, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
    · linarith only [h126, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h177 | h177
    · rcases p0_3 (m.d 0 2) (by simp) with h178 | h178
      · rcases p0_3 (m.d 0 3) (by simp) with h179 | h179
        · linarith only [h179, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h181 | h181
          · rcases p0_3 (m.d 0 5) (by simp) with h182 | h182
            · linarith only [h182, hlam, p0_0]
            · rcases h0emin with h184 | h184 | h184 | h184 | h184
              · rcases m.htr 0 1 2 (by decide) (by decide) with h185 | h185
                · linarith only [h178, h185, hlam]
                · linarith only [h179, h185, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h188 | h188
                · linarith only [h178, h188, hlam]
                · linarith only [h179, h188, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h179, h184, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h192 | h192
                · linarith only [h178, h192, hlam]
                · linarith only [h179, h192, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h184, hc01, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h196 | h196
            · linarith only [h196, hlam, p0_0]
            · rcases h0emin with h198 | h198 | h198 | h198 | h198
              · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
                · linarith only [h178, h199, hlam]
                · linarith only [h198, h199, hc12, hlam, ht01]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h202 | h202
                · linarith only [h178, h202, hlam]
                · linarith only [h179, h202, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h179, h198, hc01, hlam, p0_1]
              · linarith only [h181, h198, hc01, hlam, p0_1]
              · linarith only [h198, hc01, hlam, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h208 | h208
        · linarith only [h178, h208, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 0 5) (by simp) with h211 | h211
            · linarith only [h211, hlam, p0_0]
            · rcases h0emin with h213 | h213 | h213 | h213 | h213
              · rcases m.htr 0 1 2 (by decide) (by decide) with h214 | h214
                · rcases m.htr 0 1 3 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h216 | h216
                    · linarith only [h210, h216, hlam]
                    · linarith only [h178, h214, h216, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h178, h214, h215, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h213, h214, hc12, hlam, ht01]
              · linarith only [h178, h213, hc01, hlam, p0_1]
              · linarith only [h213, hlam, ht01, ht12, ht23, u3elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h223 | h223
                · rcases m.htr 0 1 3 (by decide) (by decide) with h224 | h224
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h225 | h225
                    · linarith only [h210, h225, hlam]
                    · linarith only [h178, h223, h225, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h178, h223, h224, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h178, h223, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h213, hc01, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h231 | h231
            · linarith only [h231, hlam, p0_0]
            · rcases h0emin with h233 | h233 | h233 | h233 | h233
              · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
                · rcases m.htr 0 1 3 (by decide) (by decide) with h235 | h235
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h236 | h236
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h237 | h237
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h238 | h238
                        · linarith only [h178, h238, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h240 | h240
                          · linarith only [h208, h238, h240, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h242 | h242
                            · linarith only [h178, h242, hlam]
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h244 | h244
                              · linarith only [h208, h244, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
                                · linarith only [h208, h246, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h248 | h248
                                  · linarith only [h210, h248, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                                    · linarith only [h234, h238, h250, hlam]
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                                      · linarith only [h240, h250, h252, hc02, hlam, hphi, ht23, u3elo1]
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                                        · linarith only [h234, h242, h254, hlam]
                                        · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                                          · linarith only [h235, h244, h256, hlam]
                                          · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                                            · linarith only [h236, h248, h258, hlam]
                                            · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                                              · linarith only [h234, h238, h244, h260, hc12, hlam, hphi, ht23, u3elo2]
                                              · linarith only [h234, h238, h260, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h237, hlam, p0_0]
                    · linarith only [h233, h236, hc14, hlam, ht01]
                  · linarith only [h178, h234, h235, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h233, h234, hc12, hlam, ht01]
              · linarith only [h178, h233, hc01, hlam, p0_1]
              · linarith only [h233, hlam, ht01, ht12, ht23, u3elo0]
              · linarith only [h210, h233, hc01, hlam, p0_1]
              · linarith only [h233, hc01, hlam, p0_1]
    · linarith only [h177, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h272 | h272
    · linarith only [h272, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h274 | h274
      · rcases p0_3 (m.d 0 3) (by simp) with h275 | h275
        · linarith only [h275, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h277 | h277
          · rcases p0_3 (m.d 0 5) (by simp) with h278 | h278
            · linarith only [h278, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h280 | h280 | h280 | h280 | h280
              · linarith only [h280, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h282 | h282
                · linarith only [h282, hlam, p0_0]
                · linarith only [h282, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h275, h280, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h286 | h286
                · linarith only [h286, hlam, p0_0]
                · linarith only [h286, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h278, h280, hc02, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h290 | h290
            · linarith only [h290, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h292 | h292 | h292 | h292 | h292
              · linarith only [h292, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h294 | h294
                · linarith only [h294, hlam, p0_0]
                · linarith only [h294, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h275, h292, hc02, hlam, p0_1]
              · linarith only [h277, h292, hc02, hlam, p0_1]
              · linarith only [h290, h292, hc02, hlam, p0_1]
      · linarith only [h274, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h302 | h302
    · rcases p0_3 (m.d 0 2) (by simp) with h303 | h303
      · rcases p0_3 (m.d 0 3) (by simp) with h304 | h304
        · linarith only [h304, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h306 | h306
          · rcases p0_3 (m.d 0 5) (by simp) with h307 | h307
            · linarith only [h307, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h309 | h309 | h309 | h309 | h309
              · rcases m.htr 0 1 2 (by decide) (by decide) with h310 | h310
                · rcases m.htr 0 1 3 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h312 | h312
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h313 | h313
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h314 | h314
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h315 | h315
                          · linarith only [h306, h315, hlam]
                          · linarith only [h311, h315, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h314, hlam, p0_0]
                      · linarith only [h309, h313, hc15, hlam, ht01]
                    · linarith only [h310, h311, h312, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h309, h311, hc13, hlam, ht01]
                · linarith only [h302, h310, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h323 | h323
                · rcases m.htr 0 1 3 (by decide) (by decide) with h324 | h324
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h326 | h326
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h328 | h328
                          · linarith only [h306, h328, hlam]
                          · linarith only [h324, h328, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h327, hlam, p0_0]
                      · linarith only [h325, h326, hc14, hlam, hphi, ht45, u5elo1]
                    · linarith only [h323, h324, h325, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h309, h323, h324, hc13, hlam, ht01]
                · linarith only [h302, h323, hlam]
              · linarith only [h309, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h337 | h337
                · rcases m.htr 0 1 3 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h340 | h340
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h341 | h341
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h342 | h342
                          · linarith only [h306, h342, hlam]
                          · linarith only [h342, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h341, hlam, p0_0]
                      · linarith only [h309, h339, h340, hc15, hlam, ht01]
                    · linarith only [h337, h338, h339, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h337, h338, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h337, hlam]
              · linarith only [h307, h309, hc02, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h351 | h351
            · linarith only [h351, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h353 | h353 | h353 | h353 | h353
              · rcases m.htr 0 1 2 (by decide) (by decide) with h354 | h354
                · rcases m.htr 0 1 3 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h357 | h357
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h358 | h358
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h359 | h359
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h360 | h360
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h361 | h361
                              · linarith only [h361, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h306, h361, hlam]
                            · linarith only [h360, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                          · linarith only [h355, h359, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h358, hlam, p0_0]
                      · linarith only [h354, h355, h357, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h354, h355, h356, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h353, h355, hc13, hlam, ht01]
                · linarith only [h302, h354, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h371 | h371
                · rcases m.htr 0 1 3 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h373 | h373
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h374 | h374
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h375 | h375
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h376 | h376
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h377 | h377
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h378 | h378
                              · linarith only [h371, h378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h306, h378, hlam]
                            · linarith only [h353, h377, hc25, hlam, ht01, ht12]
                          · linarith only [h372, h376, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h375, hlam, p0_0]
                      · linarith only [h371, h372, h374, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h371, h372, h373, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h353, h371, h372, hc13, hlam, ht01]
                · linarith only [h302, h371, hlam]
              · linarith only [h353, hc02, hlam, p0_1]
              · linarith only [h306, h353, hc02, hlam, p0_1]
              · linarith only [h351, h353, hc02, hlam, p0_1]
      · linarith only [h303, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h392 | h392
      · rcases p0_3 (m.d 0 3) (by simp) with h393 | h393
        · linarith only [h393, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h395 | h395
          · rcases p0_3 (m.d 0 5) (by simp) with h396 | h396
            · linarith only [h302, h396, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h398 | h398 | h398 | h398 | h398
              · linarith only [h302, h398, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h400 | h400
                · linarith only [h302, h400, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h400, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h398, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h404 | h404
                · linarith only [h302, h404, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h404, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h396, h398, hc02, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h408 | h408
            · linarith only [h302, h408, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h410 | h410 | h410 | h410 | h410
              · linarith only [h302, h410, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h412 | h412
                · linarith only [h302, h412, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h302, h412, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h410, hc02, hlam, p0_1]
              · linarith only [h395, h410, hc02, hlam, p0_1]
              · linarith only [h408, h410, hc02, hlam, p0_1]
      · linarith only [h392, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h419 | h419
    · rcases p0_3 (m.d 0 2) (by simp) with h420 | h420
      · rcases p0_3 (m.d 0 3) (by simp) with h421 | h421
        · linarith only [h421, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h423 | h423
          · linarith only [h423, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h425 | h425
            · linarith only [h421, h425, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h427 | h427 | h427 | h427 | h427
              · rcases m.htr 0 1 2 (by decide) (by decide) with h428 | h428
                · rcases m.htr 0 1 3 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h431 | h431
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h432 | h432
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h433 | h433
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h434 | h434
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h435 | h435
                              · linarith only [h421, h435, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h437 | h437
                                · linarith only [h428, h435, h437, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h439 | h439
                                  · linarith only [h428, h439, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                  · linarith only [h425, h439, hlam]
                            · linarith only [h434, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                          · linarith only [h433, hlam, p0_0]
                        · linarith only [h421, h429, h432, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h421, h428, h429, h431, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h421, h428, h429, h430, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h427, h429, hc13, hlam, ht01]
                · linarith only [h419, h428, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h449 | h449
                · rcases m.htr 0 1 3 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h451 | h451
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h452 | h452
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h453 | h453
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h454 | h454
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h455 | h455
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h456 | h456
                              · linarith only [h421, h456, hlam]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
                                · linarith only [h449, h456, h458, hc01, hc35, hlam, hphi, ht0b, ht5b, p0_1]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h460 | h460
                                  · linarith only [h449, h460, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                  · linarith only [h425, h460, hlam]
                            · linarith only [h427, h455, hc25, hlam, ht01, ht12]
                          · linarith only [h454, hlam, p0_0]
                        · linarith only [h421, h450, h453, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h421, h449, h450, h452, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h421, h449, h450, h451, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h427, h449, h450, hc13, hlam, ht01]
                · linarith only [h419, h449, hlam]
              · linarith only [h421, h427, hc02, hlam, p0_1]
              · linarith only [h427, hc02, hlam, p0_1]
              · linarith only [h427, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
      · linarith only [h420, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h474 | h474
      · rcases p0_3 (m.d 0 3) (by simp) with h475 | h475
        · linarith only [h419, h475, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h477 | h477
          · linarith only [h477, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h479 | h479
            · linarith only [h419, h479, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h481 | h481 | h481 | h481 | h481
              · linarith only [h419, h481, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h483 | h483
                · linarith only [h419, h483, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h419, h483, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h475, h481, hc02, hlam, p0_1]
              · linarith only [h481, hc02, hlam, p0_1]
              · linarith only [h479, h481, hc02, hlam, p0_1]
      · linarith only [h474, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h490 | h490
    · rcases p0_3 (m.d 0 2) (by simp) with h491 | h491
      · rcases p0_3 (m.d 0 3) (by simp) with h492 | h492
        · linarith only [h492, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h494 | h494
          · rcases p0_3 (m.d 0 5) (by simp) with h495 | h495
            · linarith only [h495, hlam, p0_0]
            · rcases h0emin with h497 | h497 | h497 | h497 | h497
              · rcases m.htr 0 1 2 (by decide) (by decide) with h498 | h498
                · rcases m.htr 0 1 3 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h503 | h503
                          · linarith only [h494, h503, hlam]
                          · linarith only [h492, h499, h503, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h492, h499, h502, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h497, h501, hc15, hlam, ht01]
                    · linarith only [h492, h498, h499, h500, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h497, h499, hc13, hlam, ht01]
                · linarith only [h490, h498, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h511 | h511
                · rcases m.htr 0 1 3 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h514 | h514
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h515 | h515
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h516 | h516
                          · linarith only [h494, h516, hlam]
                          · linarith only [h492, h512, h516, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h492, h512, h515, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h513, h514, hc14, hlam, hphi, ht45, u5elo1]
                    · linarith only [h492, h511, h512, h513, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h497, h511, h512, hc13, hlam, ht01]
                · linarith only [h490, h511, hlam]
              · linarith only [h492, h497, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h525 | h525
                · rcases m.htr 0 1 3 (by decide) (by decide) with h526 | h526
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h527 | h527
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h528 | h528
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h529 | h529
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h530 | h530
                          · linarith only [h494, h530, hlam]
                          · linarith only [h492, h530, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                        · linarith only [h492, h526, h529, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h497, h527, h528, hc15, hlam, ht01]
                    · linarith only [h492, h525, h526, h527, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h492, h525, h526, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h490, h525, hlam]
              · linarith only [h497, hc02, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h539 | h539
            · linarith only [h539, hlam, p0_0]
            · rcases h0emin with h541 | h541 | h541 | h541 | h541
              · rcases m.htr 0 1 2 (by decide) (by decide) with h542 | h542
                · rcases m.htr 0 1 3 (by decide) (by decide) with h543 | h543
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h544 | h544
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h545 | h545
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h546 | h546
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h547 | h547
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h548 | h548
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h549 | h549
                              · linarith only [h492, h542, h549, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h551 | h551
                                · linarith only [h492, h551, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h553 | h553
                                  · linarith only [h494, h553, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h555 | h555
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h556 | h556
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h557 | h557
                                        · rcases m.htr 1 3 4 (by decide) (by decide) with h558 | h558
                                          · linarith only [h543, h549, h558, hlam]
                                          · rcases m.htr 1 4 5 (by decide) (by decide) with h560 | h560
                                            · linarith only [h544, h553, h560, hlam]
                                            · rcases m.htr 2 3 4 (by decide) (by decide) with h562 | h562
                                              · linarith only [h543, h549, h555, h562, hlam]
                                              · rcases m.htr 2 3 5 (by decide) (by decide) with h564 | h564
                                                · linarith only [h543, h551, h555, h564, hlam]
                                                · rcases m.htr 3 4 5 (by decide) (by decide) with h566 | h566
                                                  · linarith only [h549, h553, h566, hc03, hlam, hphi, u3elo3]
                                                  · linarith only [h543, h549, h555, h566, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                        · linarith only [h542, h548, h557, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                                      · linarith only [h542, h547, h553, h555, h556, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                    · linarith only [h542, h546, h549, h553, h555, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                            · linarith only [h548, hlam, p0_0]
                          · linarith only [h547, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                        · linarith only [h492, h543, h546, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h541, h545, hc15, hlam, ht01]
                    · linarith only [h492, h542, h543, h544, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h541, h543, hc13, hlam, ht01]
                · linarith only [h490, h542, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h579 | h579
                · rcases m.htr 0 1 3 (by decide) (by decide) with h580 | h580
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h581 | h581
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h582 | h582
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h583 | h583
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h584 | h584
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h585 | h585
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h586 | h586
                              · linarith only [h492, h579, h586, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · rcases m.htr 0 3 5 (by decide) (by decide) with h588 | h588
                                · linarith only [h492, h588, hlam]
                                · rcases m.htr 0 4 5 (by decide) (by decide) with h590 | h590
                                  · linarith only [h494, h590, hlam]
                                  · rcases m.htr 1 2 3 (by decide) (by decide) with h592 | h592
                                    · rcases m.htr 1 2 4 (by decide) (by decide) with h593 | h593
                                      · rcases m.htr 1 2 5 (by decide) (by decide) with h594 | h594
                                        · rcases m.htr 1 3 4 (by decide) (by decide) with h595 | h595
                                          · linarith only [h580, h586, h595, hlam]
                                          · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                                            · linarith only [h579, h581, h590, h597, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                            · rcases m.htr 2 3 4 (by decide) (by decide) with h599 | h599
                                              · linarith only [h580, h586, h592, h599, hlam]
                                              · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                                                · linarith only [h580, h588, h592, h601, hlam]
                                                · rcases m.htr 3 4 5 (by decide) (by decide) with h603 | h603
                                                  · linarith only [h580, h586, h590, h592, h603, hc23, hlam, hphi, u3elo3]
                                                  · linarith only [h580, h586, h592, h603, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                        · linarith only [h593, h594, hc24, hlam, hphi, ht45, u5elo2]
                                      · linarith only [h579, h584, h590, h592, h593, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                    · linarith only [h579, h583, h588, h592, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                            · linarith only [h585, hlam, p0_0]
                          · linarith only [h541, h584, hc24, hlam, ht01, ht12]
                        · linarith only [h492, h580, h583, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h492, h579, h580, h582, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h492, h579, h580, h581, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h541, h579, h580, hc13, hlam, ht01]
                · linarith only [h490, h579, hlam]
              · linarith only [h492, h541, hc02, hlam, p0_1]
              · linarith only [h494, h541, hc02, hlam, p0_1]
              · linarith only [h541, hc02, hlam, p0_1]
      · linarith only [h491, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h620 | h620
      · rcases p0_3 (m.d 0 3) (by simp) with h621 | h621
        · linarith only [h490, h621, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h623 | h623
          · rcases p0_3 (m.d 0 5) (by simp) with h624 | h624
            · linarith only [h624, hlam, p0_0]
            · rcases h0emin with h626 | h626 | h626 | h626 | h626
              · linarith only [h490, h626, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h628 | h628
                · linarith only [h490, h628, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h490, h628, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h621, h626, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h632 | h632
                · linarith only [h490, h632, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h490, h632, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h626, hc02, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h636 | h636
            · linarith only [h636, hlam, p0_0]
            · rcases h0emin with h638 | h638 | h638 | h638 | h638
              · linarith only [h490, h638, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h640 | h640
                · linarith only [h490, h640, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h490, h640, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h621, h638, hc02, hlam, p0_1]
              · linarith only [h623, h638, hc02, hlam, p0_1]
              · linarith only [h638, hc02, hlam, p0_1]
      · linarith only [h620, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h652 | h652
    · linarith only [h652, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h654 | h654
      · rcases p0_3 (m.d 0 3) (by simp) with h655 | h655
        · linarith only [h655, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h657 | h657
          · rcases p0_3 (m.d 0 5) (by simp) with h658 | h658
            · linarith only [h658, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h660 | h660 | h660 | h660 | h660
              · linarith only [h654, h660, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h662 | h662
                · linarith only [h654, h662, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h654, h662, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h654, h655, h660, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h666 | h666
                · linarith only [h654, h666, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h654, h666, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h654, h658, h660, hc02, hlam, p0_1]
          · linarith only [h657, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h671 | h671
        · linarith only [h671, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h673 | h673
          · rcases p0_3 (m.d 0 5) (by simp) with h674 | h674
            · linarith only [h674, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h676 | h676 | h676 | h676 | h676
              · linarith only [h676, hc04, hlam, p0_1]
              · linarith only [h654, h676, hc04, hlam, p0_1]
              · linarith only [h671, h676, hc04, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h680 | h680
                · linarith only [h680, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h654, h680, hlam]
              · linarith only [h674, h676, hc04, hlam, p0_1]
          · linarith only [h673, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h685 | h685
    · rcases p0_3 (m.d 0 2) (by simp) with h686 | h686
      · linarith only [h686, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h688 | h688
        · linarith only [h688, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h690 | h690
          · rcases p0_3 (m.d 0 5) (by simp) with h691 | h691
            · linarith only [h691, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h693 | h693 | h693 | h693 | h693
              · rcases m.htr 0 1 2 (by decide) (by decide) with h694 | h694
                · rcases m.htr 0 1 3 (by decide) (by decide) with h695 | h695
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h696 | h696
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h697 | h697
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h698 | h698
                        · linarith only [h696, h698, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · linarith only [h688, h698, hlam]
                      · linarith only [h694, h696, h697, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h685, h696, hlam]
                  · linarith only [h693, h695, hc13, hlam, ht01]
                · linarith only [h693, h694, hc12, hlam, ht01]
              · linarith only [h685, h693, hc01, hlam, p0_1]
              · linarith only [h693, hlam, ht01, ht12, ht23, u3elo0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h707 | h707
                · rcases m.htr 0 1 3 (by decide) (by decide) with h708 | h708
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h709 | h709
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h710 | h710
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h711 | h711
                        · linarith only [h709, h711, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · linarith only [h688, h711, hlam]
                      · linarith only [h709, h710, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h685, h709, hlam]
                  · linarith only [h685, h707, h708, hc12, hlam, hphi, ht23, p0_1, u3elo1]
                · linarith only [h685, h707, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h685, h691, h693, hc01, hlam, p0_1]
          · linarith only [h690, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h720 | h720
      · linarith only [h720, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h722 | h722
        · linarith only [h685, h722, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h724 | h724
          · rcases p0_3 (m.d 0 5) (by simp) with h725 | h725
            · linarith only [h685, h725, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h727 | h727 | h727 | h727 | h727
              · linarith only [h685, h727, hc04, hlam, p0_1]
              · linarith only [h727, hc04, hlam, p0_1]
              · linarith only [h722, h727, hc04, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h731 | h731
                · linarith only [h685, h731, hlam]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h733 | h733
                  · linarith only [h731, h733, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h735 | h735
                    · linarith only [h731, h735, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h731, h735, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h725, h727, hc04, hlam, p0_1]
          · linarith only [h724, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h740 | h740
    · rcases p0_3 (m.d 0 2) (by simp) with h741 | h741
      · rcases p0_3 (m.d 0 3) (by simp) with h742 | h742
        · linarith only [h742, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h744 | h744
          · rcases p0_3 (m.d 0 5) (by simp) with h745 | h745
            · linarith only [h745, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h747 | h747 | h747 | h747 | h747
              · rcases m.htr 0 1 2 (by decide) (by decide) with h748 | h748
                · rcases m.htr 0 1 3 (by decide) (by decide) with h749 | h749
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h750 | h750
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h751 | h751
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h752 | h752
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h753 | h753
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h754 | h754
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h755 | h755
                              · linarith only [h755, hlam, p0_0]
                              · linarith only [h749, h755, hc13, hlam, hphi, p0_1, u3elo3]
                            · linarith only [h749, h753, h754, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                          · linarith only [h741, h753, hlam]
                        · linarith only [h741, h749, h752, hc13, hlam, hphi, p0_1, u3elo2]
                      · linarith only [h749, h750, h751, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h740, h750, hlam]
                  · linarith only [h747, h749, hc13, hlam, ht01]
                · linarith only [h747, h748, hc12, hlam, ht01]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h765 | h765
                · rcases m.htr 0 1 3 (by decide) (by decide) with h766 | h766
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h767 | h767
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h768 | h768
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h769 | h769
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h770 | h770
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h771 | h771
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h772 | h772
                              · linarith only [h772, hlam, p0_0]
                              · linarith only [h766, h772, hc13, hlam, hphi, p0_1, u3elo3]
                            · linarith only [h766, h770, h771, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                          · linarith only [h741, h770, hlam]
                        · linarith only [h747, h769, hc23, hlam, ht01, ht12]
                      · linarith only [h766, h767, h768, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h740, h767, hlam]
                  · linarith only [h765, h766, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h740, h765, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h740, h747, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h783 | h783
                · rcases m.htr 0 1 3 (by decide) (by decide) with h784 | h784
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h785 | h785
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h786 | h786
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h787 | h787
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h788 | h788
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h789 | h789
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
                              · linarith only [h790, hlam, p0_0]
                              · linarith only [h784, h790, hc13, hlam, hphi, p0_1, u3elo3]
                            · linarith only [h784, h788, h789, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                          · linarith only [h741, h788, hlam]
                        · linarith only [h741, h784, h787, hc13, hlam, hphi, p0_1, u3elo2]
                      · linarith only [h784, h785, h786, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h740, h785, hlam]
                  · linarith only [h740, h784, hc03, hlam, hphi, p0_1, u3elo1]
                · linarith only [h740, h783, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h747, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
          · linarith only [h744, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h802 | h802
        · linarith only [h802, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h804 | h804
          · rcases p0_3 (m.d 0 5) (by simp) with h805 | h805
            · linarith only [h741, h805, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h807 | h807 | h807 | h807 | h807
              · rcases m.htr 0 1 2 (by decide) (by decide) with h808 | h808
                · rcases m.htr 0 1 3 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h810 | h810
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h811 | h811
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h812 | h812
                        · linarith only [h741, h812, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h814 | h814
                          · linarith only [h810, h812, h814, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · linarith only [h808, h812, h814, hc12, hc24, hlam, hphi, p0_1]
                      · linarith only [h807, h811, hc15, hlam, ht01]
                    · linarith only [h740, h810, hlam]
                  · linarith only [h740, h741, h808, h809, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h807, h808, hc12, hlam, ht01]
              · linarith only [h740, h741, h807, hc01, hlam, p0_1]
              · linarith only [h740, h807, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h823 | h823
                · rcases m.htr 0 1 3 (by decide) (by decide) with h824 | h824
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h825 | h825
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h826 | h826
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h827 | h827
                        · linarith only [h741, h827, hlam]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h829 | h829
                          · linarith only [h825, h827, h829, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · linarith only [h827, h829, hc02, hc24, hlam, hphi, p0_1]
                      · linarith only [h741, h823, h825, h826, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h740, h825, hlam]
                  · linarith only [h740, h741, h823, h824, hc12, hlam, hphi, ht23, p0_1, u3elo1]
                · linarith only [h740, h741, h823, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h740, h805, h807, hc01, hlam, p0_1]
          · linarith only [h804, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h838 | h838
      · rcases p0_3 (m.d 0 3) (by simp) with h839 | h839
        · linarith only [h839, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h841 | h841
          · rcases p0_3 (m.d 0 5) (by simp) with h842 | h842
            · linarith only [h740, h842, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h844 | h844 | h844 | h844 | h844
              · linarith only [h740, h838, h844, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h846 | h846
                · linarith only [h740, h838, h846, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h740, h838, h846, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h838, h844, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h850 | h850
                · linarith only [h740, h838, h850, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h740, h838, h850, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h838, h842, h844, hc02, hlam, p0_1]
          · linarith only [h841, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h855 | h855
        · linarith only [h855, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h857 | h857
          · rcases p0_3 (m.d 0 5) (by simp) with h858 | h858
            · linarith only [h740, h858, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · rcases h0emin with h860 | h860 | h860 | h860 | h860
              · linarith only [h740, h860, hc04, hlam, p0_1]
              · linarith only [h838, h860, hc04, hlam, p0_1]
              · linarith only [h860, hc04, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h864 | h864
                · linarith only [h740, h864, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h866 | h866
                  · linarith only [h740, h866, hlam]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h868 | h868
                    · linarith only [h838, h864, h868, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h838, h864, h868, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h858, h860, hc04, hlam, p0_1]
          · linarith only [h857, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h874 | h874
    · rcases p0_3 (m.d 0 2) (by simp) with h875 | h875
      · rcases p0_3 (m.d 0 3) (by simp) with h876 | h876
        · linarith only [h876, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h878 | h878
          · rcases p0_3 (m.d 0 5) (by simp) with h879 | h879
            · linarith only [h879, hlam, p0_0]
            · rcases h0emin with h881 | h881 | h881 | h881 | h881
              · rcases m.htr 0 1 2 (by decide) (by decide) with h882 | h882
                · rcases m.htr 0 1 3 (by decide) (by decide) with h883 | h883
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h884 | h884
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h885 | h885
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h886 | h886
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h887 | h887
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h888 | h888
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h889 | h889
                              · linarith only [h876, h882, h887, h889, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h876, h883, h889, hc13, hlam, hphi, p0_1, u3elo3]
                            · linarith only [h876, h883, h887, h888, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                          · linarith only [h875, h887, hlam]
                        · linarith only [h875, h876, h883, h886, hc13, hlam, hphi, p0_1, u3elo2]
                      · linarith only [h876, h883, h884, h885, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h874, h884, hlam]
                  · linarith only [h881, h883, hc13, hlam, ht01]
                · linarith only [h881, h882, hc12, hlam, ht01]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h899 | h899
                · rcases m.htr 0 1 3 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h902 | h902
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h903 | h903
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h904 | h904
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h905 | h905
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h906 | h906
                              · linarith only [h876, h899, h904, h906, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h876, h906, hc03, hlam, hphi, p0_1, u3elo3]
                            · linarith only [h876, h900, h904, h905, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                          · linarith only [h875, h904, hlam]
                        · linarith only [h881, h903, hc23, hlam, ht01, ht12]
                      · linarith only [h876, h900, h901, h902, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h874, h901, hlam]
                  · linarith only [h899, h900, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h874, h876, h899, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h874, h876, h881, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h917 | h917
                · rcases m.htr 0 1 3 (by decide) (by decide) with h918 | h918
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h919 | h919
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h920 | h920
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h921 | h921
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h922 | h922
                          · rcases m.htr 0 2 5 (by decide) (by decide) with h923 | h923
                            · rcases m.htr 0 3 4 (by decide) (by decide) with h924 | h924
                              · linarith only [h876, h917, h922, h924, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h876, h924, hc03, hlam, hphi, p0_1, u3elo3]
                            · linarith only [h876, h918, h922, h923, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                          · linarith only [h875, h922, hlam]
                        · linarith only [h875, h876, h918, h921, hc13, hlam, hphi, p0_1, u3elo2]
                      · linarith only [h876, h918, h919, h920, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h874, h919, hlam]
                  · linarith only [h874, h876, h918, hc03, hlam, hphi, p0_1, u3elo1]
                · linarith only [h874, h876, h917, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h874, h881, hc01, hlam, p0_1]
          · linarith only [h878, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h936 | h936
        · linarith only [h875, h936, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h938 | h938
          · rcases p0_3 (m.d 0 5) (by simp) with h939 | h939
            · linarith only [h939, hlam, p0_0]
            · rcases h0emin with h941 | h941 | h941 | h941 | h941
              · rcases m.htr 0 1 2 (by decide) (by decide) with h942 | h942
                · rcases m.htr 0 1 3 (by decide) (by decide) with h943 | h943
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h944 | h944
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h945 | h945
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h946 | h946
                        · linarith only [h875, h946, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h948 | h948
                          · linarith only [h936, h944, h946, h948, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · linarith only [h936, h946, h948, hc02, hc24, hlam, hphi, p0_1]
                      · linarith only [h875, h942, h944, h945, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                    · linarith only [h874, h944, hlam]
                  · linarith only [h941, h943, hc13, hlam, ht01]
                · linarith only [h941, h942, hc12, hlam, ht01]
              · linarith only [h874, h875, h941, hc01, hlam, p0_1]
              · linarith only [h874, h936, h941, hc01, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h957 | h957
                · rcases m.htr 0 1 3 (by decide) (by decide) with h958 | h958
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h959 | h959
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h960 | h960
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h961 | h961
                        · linarith only [h875, h959, h961, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                        · rcases m.htr 0 2 4 (by decide) (by decide) with h963 | h963
                          · linarith only [h936, h959, h961, h963, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                          · linarith only [h936, h957, h961, h963, hc12, hc24, hlam, hphi, p0_1]
                      · linarith only [h936, h959, h960, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                    · linarith only [h874, h959, hlam]
                  · linarith only [h874, h875, h957, h958, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h874, h875, h957, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h874, h941, hc01, hlam, p0_1]
          · linarith only [h938, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h972 | h972
      · rcases p0_3 (m.d 0 3) (by simp) with h973 | h973
        · linarith only [h874, h973, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h975 | h975
          · rcases p0_3 (m.d 0 5) (by simp) with h976 | h976
            · linarith only [h976, hlam, p0_0]
            · rcases h0emin with h978 | h978 | h978 | h978 | h978
              · linarith only [h874, h972, h978, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h980 | h980
                · linarith only [h874, h972, h980, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h874, h972, h980, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h972, h973, h978, hc02, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h984 | h984
                · linarith only [h874, h972, h984, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h874, h972, h984, hc01, hc12, hlam, hphi, p0_1]
              · linarith only [h972, h978, hc02, hlam, p0_1]
          · linarith only [h975, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h989 | h989
        · linarith only [h874, h989, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h991 | h991
          · rcases p0_3 (m.d 0 5) (by simp) with h992 | h992
            · linarith only [h992, hlam, p0_0]
            · rcases h0emin with h994 | h994 | h994 | h994 | h994
              · linarith only [h874, h994, hc04, hlam, p0_1]
              · linarith only [h972, h994, hc04, hlam, p0_1]
              · linarith only [h989, h994, hc04, hlam, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h998 | h998
                · linarith only [h874, h998, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h1000, h972, h998, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1002 | h1002
                    · linarith only [h1002, h972, h998, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h1002, h972, h998, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h994, hc04, hlam, p0_1]
          · linarith only [h991, hlam, p0_0]
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

theorem n7l_sBT3_H_R_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h11, h13, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h13, h17, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h10, h13, h19, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                                  · linarith only [h0, h10, h13, h19, h21, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h0, h10, h12, h13, h21, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                              · linarith only [h0, h25, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h0, h11, h24, h25, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                              · linarith only [h0, h24, h28, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                                · linarith only [h10, h12, h24, h30, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                                  · linarith only [h10, h12, h32, hlam]
                                  · rcases h3bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h0, h10, h24, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h10, h12, h24, h5, h7, hlam, p34_2]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      rcases p34_3 (m.d 0 3) (by simp) with h38 | h38
                                      · rcases p34_3 (m.d 1 3) (by simp) with h39 | h39
                                        · linarith only [h1, h39, hlam]
                                        · linarith only [h10, h39, hlam]
                                      · linarith only [h38, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      rcases p34_3 (m.d 0 3) (by simp) with h43 | h43
                                      · rcases p34_3 (m.d 1 3) (by simp) with h44 | h44
                                        · linarith only [h1, h44, hlam]
                                        · linarith only [h11, h44, hlam]
                                      · linarith only [h43, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h1, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      rcases p34_3 (m.d 0 3) (by simp) with h50 | h50
                                      · rcases p34_3 (m.d 1 3) (by simp) with h51 | h51
                                        · rcases p34_3 (m.d 2 3) (by simp) with h52 | h52
                                          · linarith only [h52, h8, hlam]
                                          · rcases p34_3 (m.d 3 4) (by simp) with h54 | h54
                                            · linarith only [h10, h54, hlam]
                                            · linarith only [h24, h54, hlam]
                                        · linarith only [h51, h8, hlam]
                                      · linarith only [h3, h50, hlam]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h1, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h0, h24, h32, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h3, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h8, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h24, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h28, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h5, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h10, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h0, h10, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h32, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h6, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h11, hlam, p34_0]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h0, h11, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [h0, h11, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p34_1]
                                    · have p34_0 := h34c.1
                                      have p34_1 := h34c.2.1
                                      have p34_2 := h34c.2.2.1
                                      have p34_3 := h34c.2.2.2
                                      linarith only [hlam, p34_0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                          · linarith only [h0, h10, h11, h3, h6, h76, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                              · linarith only [h0, h11, h79, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                                · linarith only [h0, h76, h78, h8, h81, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h83 | h83
                                  · linarith only [h0, h11, h3, h6, h76, h78, h8, h83, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h3bigk with h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      rcases p85_3 (m.d 0 3) (by simp) with h87 | h87
                                      · rcases p85_3 (m.d 1 3) (by simp) with h88 | h88
                                        · linarith only [h1, h88, hlam]
                                        · rcases p85_3 (m.d 2 3) (by simp) with h90 | h90
                                          · linarith only [h3, h90, hlam]
                                          · rcases p85_3 (m.d 3 4) (by simp) with h92 | h92
                                            · linarith only [h5, h92, hlam]
                                            · rcases p85_3 (m.d 3 5) (by simp) with h94 | h94
                                              · linarith only [h6, h94, hlam]
                                              · linarith only [h11, h94, hlam]
                                      · linarith only [h1, h87, hlam]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      rcases p85_3 (m.d 0 3) (by simp) with h98 | h98
                                      · rcases p85_3 (m.d 1 3) (by simp) with h99 | h99
                                        · linarith only [h1, h99, hlam]
                                        · linarith only [h8, h99, hlam]
                                      · linarith only [h3, h98, hlam]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h10, h11, h5, h7, h83, hlam, p85_2]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h10, h11, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h1, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h11, hc23, hc35, hlam, hphi, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h11, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h11, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h3, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h8, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h79, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h5, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h10, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h78, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h83, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h6, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h10, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h3, h6, h78, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      rcases p85_3 (m.d 0 3) (by simp) with h123 | h123
                                      · rcases p85_3 (m.d 1 3) (by simp) with h124 | h124
                                        · linarith only [h11, h124, hlam]
                                        · linarith only [h10, h124, hlam]
                                      · linarith only [h123, h5, hlam]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                            · linarith only [h10, h11, h78, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
                        · linarith only [h0, h10, h130, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                            · linarith only [h0, h10, h133, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                              · linarith only [h0, h130, h135, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                                  · rcases h3bigk with h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 3) (by simp) with h141 | h141
                                      · rcases p139_3 (m.d 1 3) (by simp) with h142 | h142
                                        · linarith only [h1, h142, hlam]
                                        · rcases p139_3 (m.d 2 3) (by simp) with h144 | h144
                                          · linarith only [h144, h3, hlam]
                                          · rcases p139_3 (m.d 3 4) (by simp) with h146 | h146
                                            · linarith only [h146, h5, hlam]
                                            · linarith only [h10, h146, hlam]
                                      · linarith only [h1, h141, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 3) (by simp) with h150 | h150
                                      · rcases p139_3 (m.d 1 3) (by simp) with h151 | h151
                                        · linarith only [h1, h151, hlam]
                                        · linarith only [h151, h8, hlam]
                                      · linarith only [h150, h3, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h0, h10, h132, h3, hc01, hlam, hphi, ht0b, ht5b, p139_1, u5ehi4]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 3) (by simp) with h156 | h156
                                      · rcases p139_3 (m.d 1 3) (by simp) with h157 | h157
                                        · linarith only [h1, h157, hlam]
                                        · rcases p139_3 (m.d 2 3) (by simp) with h159 | h159
                                          · linarith only [h159, h3, hlam]
                                          · rcases p139_3 (m.d 3 4) (by simp) with h161 | h161
                                            · linarith only [h161, h5, hlam]
                                            · linarith only [h138, h161, hlam]
                                      · linarith only [h156, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h1, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h130, hc23, hc35, hlam, hphi, p139_1]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h10, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h130, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h3, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h8, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h133, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h135, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h5, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 3) (by simp) with h176 | h176
                                      · rcases p139_3 (m.d 1 3) (by simp) with h177 | h177
                                        · linarith only [h177, hlam, p139_0]
                                        · rcases p139_3 (m.d 2 3) (by simp) with h179 | h179
                                          · linarith only [h133, h179, hlam]
                                          · rcases p139_3 (m.d 3 4) (by simp) with h181 | h181
                                            · rcases p139_3 (m.d 3 5) (by simp) with h182 | h182
                                              · linarith only [h138, h182, hlam]
                                              · linarith only [h130, h182, hlam]
                                            · linarith only [h181, hlam, p139_0]
                                      · linarith only [h1, h176, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 3) (by simp) with h187 | h187
                                      · rcases p139_3 (m.d 1 3) (by simp) with h188 | h188
                                        · linarith only [h10, h188, hlam]
                                        · linarith only [h188, h8, hlam]
                                      · linarith only [h187, h3, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p139_1, u5ehi3]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h6, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 3) (by simp) with h195 | h195
                                      · rcases p139_3 (m.d 1 3) (by simp) with h196 | h196
                                        · linarith only [h196, hlam, p139_0]
                                        · rcases p139_3 (m.d 2 3) (by simp) with h198 | h198
                                          · linarith only [h135, h198, hlam]
                                          · rcases p139_3 (m.d 3 4) (by simp) with h200 | h200
                                            · rcases p139_3 (m.d 3 5) (by simp) with h201 | h201
                                              · rcases h5bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  rcases p202_3 (m.d 0 5) (by simp) with h204 | h204
                                                  · rcases p202_3 (m.d 1 5) (by simp) with h205 | h205
                                                    · linarith only [h2, h205, hlam]
                                                    · rcases p202_3 (m.d 2 5) (by simp) with h207 | h207
                                                      · linarith only [h207, h4, hlam]
                                                      · rcases p202_3 (m.d 3 5) (by simp) with h209 | h209
                                                        · linarith only [h209, h6, hlam]
                                                        · linarith only [h130, h209, hlam]
                                                  · linarith only [h2, h204, hlam]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  rcases p202_3 (m.d 0 5) (by simp) with h213 | h213
                                                  · rcases p202_3 (m.d 1 5) (by simp) with h214 | h214
                                                    · linarith only [h2, h214, hlam]
                                                    · linarith only [h214, h9, hlam]
                                                  · linarith only [h213, h4, hlam]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h0, h3, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p139_1, p202_1]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  rcases p202_3 (m.d 0 5) (by simp) with h219 | h219
                                                  · rcases p202_3 (m.d 1 5) (by simp) with h220 | h220
                                                    · linarith only [h2, h220, hlam]
                                                    · linarith only [h132, h220, hlam]
                                                  · linarith only [h219, h7, hlam]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h2, hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p202_1, u5ehi2]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h130, hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p202_1, u5ehi4]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h4, hlam, p202_1]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h9, hlam, p202_1]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h135, hlam, p202_1]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p202_1, u5ehi4]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h6, hlam, p202_1]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p202_1, u5ehi1]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p202_1, u5ehi2]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h0, h138, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p202_1, u5ehi4]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h7, hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h132, hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h137, hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [h138, hlam, p202_0]
                                                · have p202_0 := h202c.1
                                                  have p202_1 := h202c.2.1
                                                  have p202_2 := h202c.2.2.1
                                                  have p202_3 := h202c.2.2.2
                                                  linarith only [hlam, p202_0]
                                              · linarith only [h201, hlam, p139_0]
                                            · linarith only [h10, h200, hlam]
                                      · linarith only [h1, h195, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 3) (by simp) with h247 | h247
                                      · rcases p139_3 (m.d 1 3) (by simp) with h248 | h248
                                        · linarith only [h130, h248, hlam]
                                        · linarith only [h248, h8, hlam]
                                      · linarith only [h247, h3, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h138, hlam, p139_1]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                  · linarith only [h0, h10, h137, h138, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h255 | h255
                                  · rcases h3bigk with h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      rcases p256_3 (m.d 0 3) (by simp) with h258 | h258
                                      · rcases p256_3 (m.d 1 3) (by simp) with h259 | h259
                                        · linarith only [h1, h259, hlam]
                                        · rcases p256_3 (m.d 2 3) (by simp) with h261 | h261
                                          · linarith only [h261, h3, hlam]
                                          · rcases p256_3 (m.d 3 4) (by simp) with h263 | h263
                                            · linarith only [h263, h5, hlam]
                                            · linarith only [h10, h263, hlam]
                                      · linarith only [h1, h258, hlam]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h10, h132, h133, h137, h5, hlam, p256_2]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h0, h10, h132, h137, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p256_1]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      rcases p256_3 (m.d 0 3) (by simp) with h269 | h269
                                      · rcases p256_3 (m.d 1 3) (by simp) with h270 | h270
                                        · linarith only [h1, h270, hlam]
                                        · rcases p256_3 (m.d 2 3) (by simp) with h272 | h272
                                          · linarith only [h272, h3, hlam]
                                          · rcases p256_3 (m.d 3 4) (by simp) with h274 | h274
                                            · linarith only [h274, h5, hlam]
                                            · linarith only [h255, h274, hlam]
                                      · linarith only [h269, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h1, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h130, hc23, hc35, hlam, hphi, p256_1]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h10, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h130, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h3, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h8, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h133, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h135, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h5, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      rcases p256_3 (m.d 0 3) (by simp) with h289 | h289
                                      · rcases p256_3 (m.d 1 3) (by simp) with h290 | h290
                                        · linarith only [h290, hlam, p256_0]
                                        · rcases p256_3 (m.d 2 3) (by simp) with h292 | h292
                                          · linarith only [h133, h292, hlam]
                                          · rcases p256_3 (m.d 3 4) (by simp) with h294 | h294
                                            · rcases p256_3 (m.d 3 5) (by simp) with h295 | h295
                                              · linarith only [h255, h295, hlam]
                                              · linarith only [h130, h295, hlam]
                                            · linarith only [h294, hlam, p256_0]
                                      · linarith only [h1, h289, hlam]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      rcases p256_3 (m.d 0 3) (by simp) with h300 | h300
                                      · rcases p256_3 (m.d 1 3) (by simp) with h301 | h301
                                        · linarith only [h10, h301, hlam]
                                        · linarith only [h301, h8, hlam]
                                      · linarith only [h3, h300, hlam]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p256_1, u5ehi3]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h6, hlam, p256_0]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      rcases p256_3 (m.d 0 3) (by simp) with h308 | h308
                                      · rcases p256_3 (m.d 1 3) (by simp) with h309 | h309
                                        · linarith only [h309, hlam, p256_0]
                                        · rcases p256_3 (m.d 2 3) (by simp) with h311 | h311
                                          · linarith only [h135, h311, hlam]
                                          · rcases p256_3 (m.d 3 4) (by simp) with h313 | h313
                                            · rcases p256_3 (m.d 3 5) (by simp) with h314 | h314
                                              · rcases h5bigk with h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  rcases p315_3 (m.d 0 5) (by simp) with h317 | h317
                                                  · rcases p315_3 (m.d 1 5) (by simp) with h318 | h318
                                                    · linarith only [h2, h318, hlam]
                                                    · rcases p315_3 (m.d 2 5) (by simp) with h320 | h320
                                                      · linarith only [h320, h4, hlam]
                                                      · rcases p315_3 (m.d 3 5) (by simp) with h322 | h322
                                                        · linarith only [h322, h6, hlam]
                                                        · linarith only [h130, h322, hlam]
                                                  · linarith only [h2, h317, hlam]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  rcases p315_3 (m.d 0 5) (by simp) with h326 | h326
                                                  · rcases p315_3 (m.d 1 5) (by simp) with h327 | h327
                                                    · linarith only [h2, h327, hlam]
                                                    · linarith only [h327, h9, hlam]
                                                  · linarith only [h326, h4, hlam]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h0, h3, h5, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p256_1, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  rcases p315_3 (m.d 0 5) (by simp) with h332 | h332
                                                  · rcases p315_3 (m.d 1 5) (by simp) with h333 | h333
                                                    · linarith only [h2, h333, hlam]
                                                    · linarith only [h132, h333, hlam]
                                                  · linarith only [h332, h7, hlam]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h2, hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p315_1, u5ehi2]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h130, hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h130, h133, h137, hc23, hc35, hlam, hphi, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h4, hlam, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h9, hlam, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h135, hlam, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h137, hlam, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h6, hlam, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p315_1, u5ehi1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p315_1, u5ehi2]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h0, h133, h137, h255, h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p315_1]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h7, hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h132, hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h132, hc14, hlam, hphi, ht01, ht0b, ht5b, p315_1, u5ehi2]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [h255, hlam, p315_0]
                                                · have p315_0 := h315c.1
                                                  have p315_1 := h315c.2.1
                                                  have p315_2 := h315c.2.2.1
                                                  have p315_3 := h315c.2.2.2
                                                  linarith only [hlam, p315_0]
                                              · linarith only [h314, hlam, p256_0]
                                            · linarith only [h10, h313, hlam]
                                      · linarith only [h1, h308, hlam]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      rcases p256_3 (m.d 0 3) (by simp) with h360 | h360
                                      · rcases p256_3 (m.d 1 3) (by simp) with h361 | h361
                                        · linarith only [h130, h361, hlam]
                                        · linarith only [h361, h8, hlam]
                                      · linarith only [h3, h360, hlam]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [h255, hlam, p256_1]
                                    · have p256_0 := h256c.1
                                      have p256_1 := h256c.2.1
                                      have p256_2 := h256c.2.2.1
                                      have p256_3 := h256c.2.2.2
                                      linarith only [hlam, p256_0]
                                  · linarith only [h10, h132, h255, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                            · linarith only [h10, h368, h8, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h370 | h370
                              · linarith only [h0, h10, h130, h3, h370, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h372 | h372
                                · linarith only [h132, h372, h9, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h374 | h374
                                  · rcases h3bigk with h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h10, h132, h374, h5, hlam, p375_2]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h10, h132, h374, h5, h8, hlam, p375_2]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h0, h10, h132, h3, h374, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      rcases p375_3 (m.d 0 3) (by simp) with h380 | h380
                                      · rcases p375_3 (m.d 1 3) (by simp) with h381 | h381
                                        · linarith only [h1, h381, hlam]
                                        · rcases p375_3 (m.d 2 3) (by simp) with h383 | h383
                                          · linarith only [h3, h383, hlam]
                                          · rcases p375_3 (m.d 3 4) (by simp) with h385 | h385
                                            · linarith only [h385, h5, hlam]
                                            · linarith only [h374, h385, hlam]
                                      · linarith only [h380, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h1, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h10, h132, h374, hc23, hc34, hlam, hphi, p375_1]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h10, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h130, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h3, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h8, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h368, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h370, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h5, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      rcases p375_3 (m.d 0 3) (by simp) with h400 | h400
                                      · rcases p375_3 (m.d 1 3) (by simp) with h401 | h401
                                        · linarith only [h401, hlam, p375_0]
                                        · rcases p375_3 (m.d 2 3) (by simp) with h403 | h403
                                          · linarith only [h368, h403, hlam]
                                          · rcases p375_3 (m.d 3 4) (by simp) with h405 | h405
                                            · rcases p375_3 (m.d 3 5) (by simp) with h406 | h406
                                              · linarith only [h374, h406, hlam]
                                              · linarith only [h130, h406, hlam]
                                            · linarith only [h405, hlam, p375_0]
                                      · linarith only [h1, h400, hlam]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      rcases p375_3 (m.d 0 3) (by simp) with h411 | h411
                                      · rcases p375_3 (m.d 1 3) (by simp) with h412 | h412
                                        · linarith only [h10, h412, hlam]
                                        · linarith only [h412, h8, hlam]
                                      · linarith only [h3, h411, hlam]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h0, h10, h132, h3, h374, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h6, hlam, p375_0]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      rcases p375_3 (m.d 0 3) (by simp) with h419 | h419
                                      · rcases p375_3 (m.d 1 3) (by simp) with h420 | h420
                                        · linarith only [h420, hlam, p375_0]
                                        · rcases p375_3 (m.d 2 3) (by simp) with h422 | h422
                                          · linarith only [h370, h422, hlam]
                                          · rcases p375_3 (m.d 3 4) (by simp) with h424 | h424
                                            · rcases p375_3 (m.d 3 5) (by simp) with h425 | h425
                                              · rcases h5bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  rcases p426_3 (m.d 0 5) (by simp) with h428 | h428
                                                  · rcases p426_3 (m.d 1 5) (by simp) with h429 | h429
                                                    · linarith only [h2, h429, hlam]
                                                    · rcases p426_3 (m.d 2 5) (by simp) with h431 | h431
                                                      · linarith only [h4, h431, hlam]
                                                      · rcases p426_3 (m.d 3 5) (by simp) with h433 | h433
                                                        · linarith only [h433, h6, hlam]
                                                        · linarith only [h130, h433, hlam]
                                                  · linarith only [h2, h428, hlam]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  rcases p426_3 (m.d 0 5) (by simp) with h437 | h437
                                                  · rcases p426_3 (m.d 1 5) (by simp) with h438 | h438
                                                    · linarith only [h2, h438, hlam]
                                                    · linarith only [h438, h9, hlam]
                                                  · linarith only [h4, h437, hlam]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h0, h3, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  rcases p426_3 (m.d 0 5) (by simp) with h443 | h443
                                                  · rcases p426_3 (m.d 1 5) (by simp) with h444 | h444
                                                    · linarith only [h2, h444, hlam]
                                                    · rcases p426_3 (m.d 2 5) (by simp) with h446 | h446
                                                      · linarith only [h4, h446, hlam]
                                                      · rcases p426_3 (m.d 3 5) (by simp) with h448 | h448
                                                        · linarith only [h448, h6, hlam]
                                                        · linarith only [h374, h448, hlam]
                                                  · linarith only [h443, h7, hlam]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h2, hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p426_1, u5ehi2]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h130, hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h132, hlam, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h4, hlam, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h9, hlam, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h370, hlam, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h372, hlam, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h6, hlam, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p426_1, u5ehi1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p426_1, u5ehi2]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h0, h3, h372, h374, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p426_1]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h7, hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h0, h3, h5, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p426_1, u5ehi2]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p426_1, u5ehi2]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [h374, hlam, p426_0]
                                                · have p426_0 := h426c.1
                                                  have p426_1 := h426c.2.1
                                                  have p426_2 := h426c.2.2.1
                                                  have p426_3 := h426c.2.2.2
                                                  linarith only [hlam, p426_0]
                                              · linarith only [h425, hlam, p375_0]
                                            · linarith only [h10, h424, hlam]
                                      · linarith only [h1, h419, hlam]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      rcases p375_3 (m.d 0 3) (by simp) with h475 | h475
                                      · rcases p375_3 (m.d 1 3) (by simp) with h476 | h476
                                        · linarith only [h130, h476, hlam]
                                        · linarith only [h476, h8, hlam]
                                      · linarith only [h3, h475, hlam]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [h374, hlam, p375_1]
                                    · have p375_0 := h375c.1
                                      have p375_1 := h375c.2.1
                                      have p375_2 := h375c.2.2.1
                                      have p375_3 := h375c.2.2.2
                                      linarith only [hlam, p375_0]
                                  · rcases h3bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h10, h374, h5, h7, hlam, p482_2]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h10, h374, h5, h7, h8, hlam, p482_2]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      rcases p482_3 (m.d 0 3) (by simp) with h486 | h486
                                      · rcases p482_3 (m.d 1 3) (by simp) with h487 | h487
                                        · linarith only [h1, h487, hlam]
                                        · rcases p482_3 (m.d 2 3) (by simp) with h489 | h489
                                          · linarith only [h3, h489, hlam]
                                          · rcases p482_3 (m.d 3 4) (by simp) with h491 | h491
                                            · linarith only [h491, hlam, p482_0]
                                            · rcases p482_3 (m.d 3 5) (by simp) with h493 | h493
                                              · linarith only [h493, h6, hlam]
                                              · linarith only [h374, h493, hlam]
                                      · linarith only [h486, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      rcases p482_3 (m.d 0 3) (by simp) with h497 | h497
                                      · rcases p482_3 (m.d 1 3) (by simp) with h498 | h498
                                        · linarith only [h1, h498, hlam]
                                        · rcases p482_3 (m.d 2 3) (by simp) with h500 | h500
                                          · linarith only [h3, h500, hlam]
                                          · rcases p482_3 (m.d 3 4) (by simp) with h502 | h502
                                            · linarith only [h5, h502, hlam]
                                            · rcases p482_3 (m.d 3 5) (by simp) with h504 | h504
                                              · linarith only [h504, hlam, p482_0]
                                              · rcases h5bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [hlam, p506_0]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  rcases p506_3 (m.d 0 5) (by simp) with h508 | h508
                                                  · rcases p506_3 (m.d 1 5) (by simp) with h509 | h509
                                                    · linarith only [h2, h509, hlam]
                                                    · rcases p506_3 (m.d 2 5) (by simp) with h511 | h511
                                                      · linarith only [h4, h511, hlam]
                                                      · rcases p506_3 (m.d 3 5) (by simp) with h513 | h513
                                                        · linarith only [h513, h6, hlam]
                                                        · linarith only [h130, h513, hlam]
                                                  · linarith only [h2, h508, hlam]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  rcases p506_3 (m.d 0 5) (by simp) with h517 | h517
                                                  · rcases p506_3 (m.d 1 5) (by simp) with h518 | h518
                                                    · linarith only [h2, h518, hlam]
                                                    · linarith only [h518, h9, hlam]
                                                  · linarith only [h4, h517, hlam]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  rcases p506_3 (m.d 0 5) (by simp) with h522 | h522
                                                  · rcases p506_3 (m.d 1 5) (by simp) with h523 | h523
                                                    · linarith only [h2, h523, hlam]
                                                    · rcases p506_3 (m.d 2 5) (by simp) with h525 | h525
                                                      · linarith only [h4, h525, hlam]
                                                      · rcases p506_3 (m.d 3 5) (by simp) with h527 | h527
                                                        · linarith only [h527, h6, hlam]
                                                        · rcases p506_3 (m.d 4 5) (by simp) with h529 | h529
                                                          · linarith only [h529, h7, hlam]
                                                          · linarith only [h374, h529, hlam]
                                                  · linarith only [h522, h6, hlam]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h0, h10, h3, h374, h5, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h2, hlam, p506_0]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [hlam, p506_0]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p506_1, u5ehi2]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h130, hlam, p506_0]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h132, hlam, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h4, hlam, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h9, hlam, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [hlam, p506_0]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h370, hlam, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h372, hlam, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h6, hlam, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p482_1, p506_1, u5ehi1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p482_1, p506_1, u5ehi2]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [hlam, p506_0]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h374, hlam, p506_1]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h7, hlam, p506_0]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h0, h3, h5, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p506_1, u5ehi2]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p506_1, u5ehi2]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p506_1, u5ehi3]
                                                · have p506_0 := h506c.1
                                                  have p506_1 := h506c.2.1
                                                  have p506_2 := h506c.2.2.1
                                                  have p506_3 := h506c.2.2.2
                                                  linarith only [hlam, p506_0]
                                      · linarith only [h497, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h1, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h10, hc23, hc34, hlam, hphi, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h10, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h130, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h3, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h8, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h368, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h370, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h5, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h0, h3, h374, h5, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h0, h3, h374, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h374, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h6, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      rcases p482_3 (m.d 0 3) (by simp) with h571 | h571
                                      · rcases p482_3 (m.d 1 3) (by simp) with h572 | h572
                                        · linarith only [h572, hlam, p482_0]
                                        · rcases p482_3 (m.d 2 3) (by simp) with h574 | h574
                                          · linarith only [h370, h574, hlam]
                                          · rcases p482_3 (m.d 3 4) (by simp) with h576 | h576
                                            · linarith only [h374, h576, hlam]
                                            · linarith only [h10, h576, hlam]
                                      · linarith only [h1, h571, hlam]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      rcases p482_3 (m.d 0 3) (by simp) with h580 | h580
                                      · rcases p482_3 (m.d 1 3) (by simp) with h581 | h581
                                        · linarith only [h130, h581, hlam]
                                        · linarith only [h581, h8, hlam]
                                      · linarith only [h3, h580, hlam]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h10, h8, hc23, hc35, hlam, hphi, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h587 | h587
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h588 | h588
                        · linarith only [h0, h4, h588, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h590 | h590
                          · linarith only [h0, h4, h587, h590, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h592 | h592
                            · linarith only [h0, h4, h592, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h4, h587, h592, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
                        · linarith only [h0, h4, h595, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h598 | h598
                            · linarith only [h0, h3, h587, h597, h598, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h600 | h600
                              · linarith only [h0, h4, h595, h600, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h602 | h602
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h603 | h603
                                  · rcases h3bigk with h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      rcases p604_3 (m.d 0 3) (by simp) with h606 | h606
                                      · rcases p604_3 (m.d 1 3) (by simp) with h607 | h607
                                        · linarith only [h1, h607, hlam]
                                        · rcases p604_3 (m.d 2 3) (by simp) with h609 | h609
                                          · linarith only [h3, h609, hlam]
                                          · rcases p604_3 (m.d 3 4) (by simp) with h611 | h611
                                            · linarith only [h5, h611, hlam]
                                            · linarith only [h587, h611, hlam]
                                      · linarith only [h1, h606, hlam]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h5, h598, h602, h8, h9, hlam, p604_2]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h0, h3, h598, h602, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p604_1]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h0, h3, h600, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p604_1]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h1, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h595, hc23, hc35, hlam, hphi, p604_1]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h587, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h595, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h3, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h8, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h598, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h600, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h5, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      rcases p604_3 (m.d 0 3) (by simp) with h629 | h629
                                      · rcases p604_3 (m.d 1 3) (by simp) with h630 | h630
                                        · linarith only [h630, hlam, p604_0]
                                        · rcases p604_3 (m.d 2 3) (by simp) with h632 | h632
                                          · linarith only [h598, h632, hlam]
                                          · rcases p604_3 (m.d 3 4) (by simp) with h634 | h634
                                            · rcases p604_3 (m.d 3 5) (by simp) with h635 | h635
                                              · linarith only [h603, h635, hlam]
                                              · linarith only [h595, h635, hlam]
                                            · linarith only [h634, hlam, p604_0]
                                      · linarith only [h1, h629, hlam]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      rcases p604_3 (m.d 0 3) (by simp) with h640 | h640
                                      · rcases p604_3 (m.d 1 3) (by simp) with h641 | h641
                                        · linarith only [h587, h641, hlam]
                                        · linarith only [h641, h8, hlam]
                                      · linarith only [h3, h640, hlam]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p604_1, u5ehi3]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h6, hlam, p604_0]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      rcases p604_3 (m.d 0 3) (by simp) with h648 | h648
                                      · rcases p604_3 (m.d 1 3) (by simp) with h649 | h649
                                        · linarith only [h649, hlam, p604_0]
                                        · rcases p604_3 (m.d 2 3) (by simp) with h651 | h651
                                          · linarith only [h600, h651, hlam]
                                          · rcases p604_3 (m.d 3 4) (by simp) with h653 | h653
                                            · rcases p604_3 (m.d 3 5) (by simp) with h654 | h654
                                              · rcases h5bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  rcases p655_3 (m.d 0 5) (by simp) with h657 | h657
                                                  · rcases p655_3 (m.d 1 5) (by simp) with h658 | h658
                                                    · linarith only [h2, h658, hlam]
                                                    · rcases p655_3 (m.d 2 5) (by simp) with h660 | h660
                                                      · linarith only [h4, h660, hlam]
                                                      · linarith only [h660, h9, hlam]
                                                  · linarith only [h2, h657, hlam]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h0, h3, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h0, h3, h5, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p604_1, p655_1]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  rcases p655_3 (m.d 0 5) (by simp) with h666 | h666
                                                  · rcases p655_3 (m.d 1 5) (by simp) with h667 | h667
                                                    · linarith only [h2, h667, hlam]
                                                    · linarith only [h597, h667, hlam]
                                                  · linarith only [h666, h7, hlam]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h2, hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h9, hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h595, hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p655_1, u5ehi4]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h4, hlam, p655_1]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p655_1, u5ehi1]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h600, hlam, p655_1]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h0, h3, h5, h598, h602, hc01, hlam, hphi, ht0b, ht5b, p655_1, u5ehi4]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h6, hlam, p655_1]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h8, h9, hc23, hc35, hlam, hphi, p655_1]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p655_1, u5ehi2]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h0, h3, h5, h603, hc01, hlam, hphi, ht0b, ht5b, p655_1, u5ehi4]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h7, hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h597, hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h602, hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [h603, hlam, p655_0]
                                                · have p655_0 := h655c.1
                                                  have p655_1 := h655c.2.1
                                                  have p655_2 := h655c.2.2.1
                                                  have p655_3 := h655c.2.2.2
                                                  linarith only [hlam, p655_0]
                                              · linarith only [h654, hlam, p604_0]
                                            · linarith only [h587, h653, hlam]
                                      · linarith only [h1, h648, hlam]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      rcases p604_3 (m.d 0 3) (by simp) with h694 | h694
                                      · rcases p604_3 (m.d 1 3) (by simp) with h695 | h695
                                        · linarith only [h595, h695, hlam]
                                        · linarith only [h695, h8, hlam]
                                      · linarith only [h3, h694, hlam]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [h603, hlam, p604_1]
                                    · have p604_0 := h604c.1
                                      have p604_1 := h604c.2.1
                                      have p604_2 := h604c.2.2.1
                                      have p604_3 := h604c.2.2.2
                                      linarith only [hlam, p604_0]
                                  · linarith only [h587, h597, h603, hlam]
                                · linarith only [h587, h597, h602, h8, h9, hc23, hc34, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                            · linarith only [h0, h4, h703, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h705 | h705
                              · linarith only [h0, h4, h705, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h707 | h707
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h708 | h708
                                  · rcases h3bigk with h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h5, h587, h597, h703, h707, hlam, p709_2]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h5, h587, h597, h703, h707, h8, hlam, p709_2]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h0, h3, h587, h597, h703, h707, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h0, h3, h705, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h1, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h587, h597, h707, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h587, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h595, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h3, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h8, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h703, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h705, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h5, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      rcases p709_3 (m.d 0 3) (by simp) with h726 | h726
                                      · rcases p709_3 (m.d 1 3) (by simp) with h727 | h727
                                        · linarith only [h727, hlam, p709_0]
                                        · rcases p709_3 (m.d 2 3) (by simp) with h729 | h729
                                          · linarith only [h703, h729, hlam]
                                          · rcases p709_3 (m.d 3 4) (by simp) with h731 | h731
                                            · rcases p709_3 (m.d 3 5) (by simp) with h732 | h732
                                              · linarith only [h708, h732, hlam]
                                              · linarith only [h595, h732, hlam]
                                            · linarith only [h731, hlam, p709_0]
                                      · linarith only [h1, h726, hlam]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      rcases p709_3 (m.d 0 3) (by simp) with h737 | h737
                                      · rcases p709_3 (m.d 1 3) (by simp) with h738 | h738
                                        · linarith only [h587, h738, hlam]
                                        · linarith only [h738, h8, hlam]
                                      · linarith only [h3, h737, hlam]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h0, h3, h5, h705, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h6, hlam, p709_0]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      rcases p709_3 (m.d 0 3) (by simp) with h745 | h745
                                      · rcases p709_3 (m.d 1 3) (by simp) with h746 | h746
                                        · linarith only [h746, hlam, p709_0]
                                        · rcases p709_3 (m.d 2 3) (by simp) with h748 | h748
                                          · linarith only [h705, h748, hlam]
                                          · rcases p709_3 (m.d 3 4) (by simp) with h750 | h750
                                            · rcases p709_3 (m.d 3 5) (by simp) with h751 | h751
                                              · rcases h5bigk with h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  rcases p752_3 (m.d 0 5) (by simp) with h754 | h754
                                                  · rcases p752_3 (m.d 1 5) (by simp) with h755 | h755
                                                    · linarith only [h2, h755, hlam]
                                                    · rcases p752_3 (m.d 2 5) (by simp) with h757 | h757
                                                      · linarith only [h4, h757, hlam]
                                                      · linarith only [h757, h9, hlam]
                                                  · linarith only [h2, h754, hlam]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h0, h3, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h0, h3, h5, h7, h705, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  rcases p752_3 (m.d 0 5) (by simp) with h763 | h763
                                                  · rcases p752_3 (m.d 1 5) (by simp) with h764 | h764
                                                    · linarith only [h2, h764, hlam]
                                                    · rcases p752_3 (m.d 2 5) (by simp) with h766 | h766
                                                      · linarith only [h4, h766, hlam]
                                                      · linarith only [h707, h766, hlam]
                                                  · linarith only [h7, h763, hlam]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h2, hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h9, hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h595, hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h597, hlam, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h4, hlam, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p752_1, u5ehi1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h705, hlam, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h0, h3, h5, h587, h597, h703, h707, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h6, hlam, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p752_1, u5ehi2]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h0, h3, h5, h587, h597, h708, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h7, hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h8, h9, hc23, hc45, hlam, hphi, ht34, p752_1]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h707, hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [h708, hlam, p752_0]
                                                · have p752_0 := h752c.1
                                                  have p752_1 := h752c.2.1
                                                  have p752_2 := h752c.2.2.1
                                                  have p752_3 := h752c.2.2.2
                                                  linarith only [hlam, p752_0]
                                              · linarith only [h751, hlam, p709_0]
                                            · linarith only [h587, h750, hlam]
                                      · linarith only [h1, h745, hlam]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      rcases p709_3 (m.d 0 3) (by simp) with h793 | h793
                                      · rcases p709_3 (m.d 1 3) (by simp) with h794 | h794
                                        · linarith only [h595, h794, hlam]
                                        · linarith only [h794, h8, hlam]
                                      · linarith only [h3, h793, hlam]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [h708, hlam, p709_1]
                                    · have p709_0 := h709c.1
                                      have p709_1 := h709c.2.1
                                      have p709_2 := h709c.2.2.1
                                      have p709_3 := h709c.2.2.2
                                      linarith only [hlam, p709_0]
                                  · linarith only [h703, h707, h708, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h801 | h801
                                  · linarith only [h0, h3, h5, h707, h8, h801, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases h3bigk with h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h5, h587, h7, h801, hlam, p803_2]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h6, h705, h8, h9, hlam, p803_2]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      rcases p803_3 (m.d 0 3) (by simp) with h807 | h807
                                      · rcases p803_3 (m.d 1 3) (by simp) with h808 | h808
                                        · linarith only [h1, h808, hlam]
                                        · rcases p803_3 (m.d 2 3) (by simp) with h810 | h810
                                          · linarith only [h3, h810, hlam]
                                          · rcases p803_3 (m.d 3 4) (by simp) with h812 | h812
                                            · linarith only [h812, hlam, p803_0]
                                            · rcases p803_3 (m.d 3 5) (by simp) with h814 | h814
                                              · linarith only [h6, h814, hlam]
                                              · linarith only [h801, h814, hlam]
                                      · linarith only [h807, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h0, h3, h705, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h1, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h0, h3, h5, h587, h7, h801, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h587, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h595, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h3, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h8, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h703, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h705, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h5, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h0, h3, h5, h7, h801, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h0, h3, h5, h7, h801, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h801, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h6, hlam, p803_0]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      rcases p803_3 (m.d 0 3) (by simp) with h835 | h835
                                      · rcases p803_3 (m.d 1 3) (by simp) with h836 | h836
                                        · linarith only [h836, hlam, p803_0]
                                        · rcases p803_3 (m.d 2 3) (by simp) with h838 | h838
                                          · linarith only [h705, h838, hlam]
                                          · rcases p803_3 (m.d 3 4) (by simp) with h840 | h840
                                            · linarith only [h801, h840, hlam]
                                            · linarith only [h587, h840, hlam]
                                      · linarith only [h1, h835, hlam]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      rcases p803_3 (m.d 0 3) (by simp) with h844 | h844
                                      · rcases p803_3 (m.d 1 3) (by simp) with h845 | h845
                                        · linarith only [h595, h845, hlam]
                                        · linarith only [h8, h845, hlam]
                                      · linarith only [h3, h844, hlam]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [h0, h3, h587, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                                    · have p803_0 := h803c.1
                                      have p803_1 := h803c.2.1
                                      have p803_2 := h803c.2.2.1
                                      have p803_3 := h803c.2.2.2
                                      linarith only [hlam, p803_0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h851 | h851
                    · linarith only [h0, h3, h8, h851, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h853 | h853
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h854 | h854
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h855 | h855
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h856 | h856
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h857 | h857
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h858 | h858
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h859 | h859
                                  · linarith only [h0, h3, h8, h853, h859, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h3bigk with h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h0, h3, h854, hc01, hlam, hphi, ht0b, ht5b, p861_1, u5ehi3]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h0, h3, h8, h854, hc01, hlam, hphi, ht0b, ht5b, p861_1, u5ehi3]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      rcases p861_3 (m.d 0 3) (by simp) with h865 | h865
                                      · rcases p861_3 (m.d 1 3) (by simp) with h866 | h866
                                        · linarith only [h1, h866, hlam]
                                        · linarith only [h853, h866, hlam]
                                      · linarith only [h865, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      rcases p861_3 (m.d 0 3) (by simp) with h870 | h870
                                      · rcases p861_3 (m.d 1 3) (by simp) with h871 | h871
                                        · linarith only [h1, h871, hlam]
                                        · linarith only [h854, h871, hlam]
                                      · linarith only [h870, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h1, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h8, hlam, p861_1]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      rcases p861_3 (m.d 0 3) (by simp) with h878 | h878
                                      · rcases p861_3 (m.d 1 3) (by simp) with h879 | h879
                                        · rcases p861_3 (m.d 2 3) (by simp) with h880 | h880
                                          · rcases p861_3 (m.d 3 4) (by simp) with h881 | h881
                                            · linarith only [h881, hlam, p861_0]
                                            · rcases p861_3 (m.d 3 5) (by simp) with h883 | h883
                                              · linarith only [h854, h883, hlam]
                                              · linarith only [h859, h883, hlam]
                                          · linarith only [h856, h880, hlam]
                                        · linarith only [h879, hlam, p861_0]
                                      · linarith only [h5, h878, hlam]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p861_1, u5ehi3]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h3, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h853, h855, h859, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p861_1]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      rcases p861_3 (m.d 0 3) (by simp) with h893 | h893
                                      · rcases p861_3 (m.d 1 3) (by simp) with h894 | h894
                                        · linarith only [h8, h894, hlam]
                                        · linarith only [h853, h894, hlam]
                                      · linarith only [h5, h893, hlam]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p861_1, u5ehi3]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h5, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h853, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h856, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h859, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h6, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h854, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h857, hlam, p861_0]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [h1, h854, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p861_1]
                                    · have p861_0 := h861c.1
                                      have p861_1 := h861c.2.1
                                      have p861_2 := h861c.2.2.1
                                      have p861_3 := h861c.2.2.2
                                      linarith only [hlam, p861_0]
                                · linarith only [h851, h855, h858, hlam]
                              · linarith only [h2, h8, h853, h854, h855, h857, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h5, h8, h853, h855, h856, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h912 | h912
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h913 | h913
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h914 | h914
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h915 | h915
                                  · linarith only [h853, h855, h915, hlam]
                                  · rcases h3bigk with h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h0, h3, h854, hc01, hlam, hphi, ht0b, ht5b, p917_1, u5ehi3]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h0, h3, h855, h912, h914, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      rcases p917_3 (m.d 0 3) (by simp) with h921 | h921
                                      · rcases p917_3 (m.d 1 3) (by simp) with h922 | h922
                                        · linarith only [h1, h922, hlam]
                                        · linarith only [h853, h922, hlam]
                                      · linarith only [h921, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      rcases p917_3 (m.d 0 3) (by simp) with h926 | h926
                                      · rcases p917_3 (m.d 1 3) (by simp) with h927 | h927
                                        · linarith only [h1, h927, hlam]
                                        · linarith only [h854, h927, hlam]
                                      · linarith only [h926, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h1, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h8, hlam, p917_1]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      rcases p917_3 (m.d 0 3) (by simp) with h934 | h934
                                      · rcases p917_3 (m.d 1 3) (by simp) with h935 | h935
                                        · rcases p917_3 (m.d 2 3) (by simp) with h936 | h936
                                          · rcases p917_3 (m.d 3 4) (by simp) with h937 | h937
                                            · linarith only [h937, hlam, p917_0]
                                            · rcases p917_3 (m.d 3 5) (by simp) with h939 | h939
                                              · linarith only [h854, h939, hlam]
                                              · linarith only [h915, h939, hlam]
                                          · linarith only [h912, h936, hlam]
                                        · linarith only [h935, hlam, p917_0]
                                      · linarith only [h5, h934, hlam]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p917_1, u5ehi3]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h3, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h0, h3, h853, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      rcases p917_3 (m.d 0 3) (by simp) with h949 | h949
                                      · rcases p917_3 (m.d 1 3) (by simp) with h950 | h950
                                        · linarith only [h8, h950, hlam]
                                        · linarith only [h853, h950, hlam]
                                      · linarith only [h5, h949, hlam]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p917_1, u5ehi3]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h5, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h853, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h912, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h915, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h6, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h854, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h913, hlam, p917_0]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [h1, h854, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                                    · have p917_0 := h917c.1
                                      have p917_1 := h917c.2.1
                                      have p917_2 := h917c.2.2.1
                                      have p917_3 := h917c.2.2.2
                                      linarith only [hlam, p917_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h965 | h965
                                  · linarith only [h0, h3, h8, h851, h853, h914, h965, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h3bigk with h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h0, h3, h854, hc01, hlam, hphi, ht0b, ht5b, p967_1, u5ehi3]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h0, h3, h8, h854, hc01, hlam, hphi, ht0b, ht5b, p967_1, u5ehi3]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      rcases p967_3 (m.d 0 3) (by simp) with h971 | h971
                                      · rcases p967_3 (m.d 1 3) (by simp) with h972 | h972
                                        · linarith only [h1, h972, hlam]
                                        · linarith only [h853, h972, hlam]
                                      · linarith only [h971, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      rcases p967_3 (m.d 0 3) (by simp) with h976 | h976
                                      · rcases p967_3 (m.d 1 3) (by simp) with h977 | h977
                                        · linarith only [h1, h977, hlam]
                                        · linarith only [h854, h977, hlam]
                                      · linarith only [h976, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h1, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h8, hlam, p967_1]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      rcases p967_3 (m.d 0 3) (by simp) with h984 | h984
                                      · rcases p967_3 (m.d 1 3) (by simp) with h985 | h985
                                        · rcases p967_3 (m.d 2 3) (by simp) with h986 | h986
                                          · rcases p967_3 (m.d 3 4) (by simp) with h987 | h987
                                            · linarith only [h987, hlam, p967_0]
                                            · rcases p967_3 (m.d 3 5) (by simp) with h989 | h989
                                              · linarith only [h854, h989, hlam]
                                              · linarith only [h965, h989, hlam]
                                          · linarith only [h912, h986, hlam]
                                        · linarith only [h985, hlam, p967_0]
                                      · linarith only [h5, h984, hlam]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p967_1, u5ehi3]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h3, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h0, h3, h853, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p967_1]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      rcases p967_3 (m.d 0 3) (by simp) with h999 | h999
                                      · rcases p967_3 (m.d 1 3) (by simp) with h1000 | h1000
                                        · linarith only [h1000, h8, hlam]
                                        · linarith only [h1000, h853, hlam]
                                      · linarith only [h5, h999, hlam]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p967_1, u5ehi3]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h5, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h853, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h912, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h965, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h6, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h854, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h913, hlam, p967_0]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [h1, h854, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p967_1]
                                    · have p967_0 := h967c.1
                                      have p967_1 := h967c.2.1
                                      have p967_2 := h967c.2.2.1
                                      have p967_3 := h967c.2.2.2
                                      linarith only [hlam, p967_0]
                              · linarith only [h1, h8, h854, h913, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h3, h5, h8, h854, h912, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1017 | h1017
                          · linarith only [h0, h1017, h3, h6, h853, h854, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1019 | h1019
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1020 | h1020
                              · linarith only [h0, h1020, h3, h853, h854, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1022 | h1022
                                · linarith only [h0, h1017, h1019, h1020, h1022, h3, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1024 | h1024
                                  · linarith only [h1, h1022, h1024, h853, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h3bigk with h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      rcases p1026_3 (m.d 0 3) (by simp) with h1028 | h1028
                                      · rcases p1026_3 (m.d 1 3) (by simp) with h1029 | h1029
                                        · linarith only [h1, h1029, hlam]
                                        · rcases p1026_3 (m.d 2 3) (by simp) with h1031 | h1031
                                          · linarith only [h1031, h3, hlam]
                                          · linarith only [h1031, h8, hlam]
                                      · linarith only [h1, h1028, hlam]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      rcases p1026_3 (m.d 0 3) (by simp) with h1035 | h1035
                                      · rcases p1026_3 (m.d 1 3) (by simp) with h1036 | h1036
                                        · linarith only [h1, h1036, hlam]
                                        · rcases p1026_3 (m.d 2 3) (by simp) with h1038 | h1038
                                          · linarith only [h1038, h3, hlam]
                                          · rcases p1026_3 (m.d 3 4) (by simp) with h1040 | h1040
                                            · linarith only [h1040, h5, hlam]
                                            · rcases p1026_3 (m.d 3 5) (by simp) with h1042 | h1042
                                              · linarith only [h1042, h6, hlam]
                                              · linarith only [h1020, h1042, hlam]
                                      · linarith only [h1035, h3, hlam]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h1020, h1024, h5, h7, h8, h853, hlam, p1026_2]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h0, h1020, h3, h8, h853, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1026_1]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h1, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h8, hlam, p1026_1]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h1020, h1024, h8, hc34, hc45, hlam, hphi, p1026_1]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h854, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h3, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h1020, hc13, hc35, hlam, hphi, p1026_1]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h0, h1020, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1026_1]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h1020, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h5, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h853, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h1019, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h1024, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h6, hlam, p1026_0]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h0, h3, h6, h853, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1026_1]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1026_1]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      rcases p1026_3 (m.d 0 3) (by simp) with h1066 | h1066
                                      · rcases p1026_3 (m.d 1 3) (by simp) with h1067 | h1067
                                        · linarith only [h1067, h854, hlam]
                                        · linarith only [h1067, h853, hlam]
                                      · linarith only [h1066, h5, hlam]
                                    · have p1026_0 := h1026c.1
                                      have p1026_1 := h1026c.2.1
                                      have p1026_2 := h1026c.2.2.1
                                      have p1026_3 := h1026c.2.2.2
                                      linarith only [hlam, p1026_0]
                            · linarith only [h1, h1019, h8, h853, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1073 | h1073
                        · linarith only [h0, h1073, h3, h5, h853, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1075 | h1075
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1076 | h1076
                            · linarith only [h0, h1075, h1076, h3, h853, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1078 | h1078
                              · linarith only [h0, h1076, h1078, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1080 | h1080
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1081 | h1081
                                  · rcases h3bigk with h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c | h1082c
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      rcases p1082_3 (m.d 0 3) (by simp) with h1084 | h1084
                                      · rcases p1082_3 (m.d 1 3) (by simp) with h1085 | h1085
                                        · linarith only [h1, h1085, hlam]
                                        · rcases p1082_3 (m.d 2 3) (by simp) with h1087 | h1087
                                          · linarith only [h1087, h3, hlam]
                                          · linarith only [h1087, h8, hlam]
                                      · linarith only [h1, h1084, hlam]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      rcases p1082_3 (m.d 0 3) (by simp) with h1091 | h1091
                                      · rcases p1082_3 (m.d 1 3) (by simp) with h1092 | h1092
                                        · linarith only [h1, h1092, hlam]
                                        · rcases p1082_3 (m.d 2 3) (by simp) with h1094 | h1094
                                          · linarith only [h1094, h3, hlam]
                                          · rcases p1082_3 (m.d 3 4) (by simp) with h1096 | h1096
                                            · linarith only [h1096, h5, hlam]
                                            · linarith only [h1076, h1096, hlam]
                                      · linarith only [h1091, h3, hlam]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h0, h1078, h1081, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1082_1]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h0, h1078, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1082_1]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h1, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h8, hlam, p1082_1]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h853, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h1073, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h3, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h1078, h1081, hc13, hc34, hlam, hphi, p1082_1]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h1076, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h1078, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h5, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      rcases p1082_3 (m.d 0 3) (by simp) with h1113 | h1113
                                      · rcases p1082_3 (m.d 1 3) (by simp) with h1114 | h1114
                                        · linarith only [h1114, hlam, p1082_0]
                                        · rcases p1082_3 (m.d 2 3) (by simp) with h1116 | h1116
                                          · linarith only [h1076, h1116, hlam]
                                          · linarith only [h1116, h8, hlam]
                                      · linarith only [h1, h1113, hlam]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h0, h3, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1082_1]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h0, h1078, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p1082_1, u5ehi2]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h6, hlam, p1082_0]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      rcases p1082_3 (m.d 0 3) (by simp) with h1124 | h1124
                                      · rcases p1082_3 (m.d 1 3) (by simp) with h1125 | h1125
                                        · linarith only [h1125, hlam, p1082_0]
                                        · rcases p1082_3 (m.d 2 3) (by simp) with h1127 | h1127
                                          · linarith only [h1078, h1127, hlam]
                                          · linarith only [h1127, h8, hlam]
                                      · linarith only [h1, h1124, hlam]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h8, hc12, hc35, hlam, hphi, ht23, p1082_1]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [h1081, hlam, p1082_1]
                                    · have p1082_0 := h1082c.1
                                      have p1082_1 := h1082c.2.1
                                      have p1082_2 := h1082c.2.2.1
                                      have p1082_3 := h1082c.2.2.2
                                      linarith only [hlam, p1082_0]
                                  · linarith only [h1075, h1081, h853, hlam]
                                · linarith only [h0, h1075, h1076, h1080, h3, h5, h8, h853, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1136 | h1136
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1137 | h1137
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1138 | h1138
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1139 | h1139
                                  · linarith only [h0, h1075, h1136, h1139, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h1136, h1138, h1139, h3, h8, h853, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1142 | h1142
                                  · linarith only [h1136, h1138, h1142, hlam]
                                  · rcases h3bigk with h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1136, h1138, h5, h7, h853, hlam, p1144_2]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1073, h1137, hc03, hlam, hphi, ht0b, ht5b, p1144_1, u5ehi1]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      rcases p1144_3 (m.d 0 3) (by simp) with h1148 | h1148
                                      · rcases p1144_3 (m.d 1 3) (by simp) with h1149 | h1149
                                        · linarith only [h1, h1149, hlam]
                                        · rcases p1144_3 (m.d 2 3) (by simp) with h1151 | h1151
                                          · linarith only [h1151, h3, hlam]
                                          · linarith only [h1136, h1151, hlam]
                                      · linarith only [h1148, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      rcases p1144_3 (m.d 0 3) (by simp) with h1155 | h1155
                                      · rcases p1144_3 (m.d 1 3) (by simp) with h1156 | h1156
                                        · linarith only [h1, h1156, hlam]
                                        · rcases p1144_3 (m.d 2 3) (by simp) with h1158 | h1158
                                          · linarith only [h1158, h3, hlam]
                                          · linarith only [h1137, h1158, hlam]
                                      · linarith only [h1155, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h8, hlam, p1144_1]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h853, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1073, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h3, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      rcases p1144_3 (m.d 0 3) (by simp) with h1168 | h1168
                                      · rcases p1144_3 (m.d 1 3) (by simp) with h1169 | h1169
                                        · linarith only [h1169, h8, hlam]
                                        · rcases p1144_3 (m.d 2 3) (by simp) with h1171 | h1171
                                          · rcases p1144_3 (m.d 3 4) (by simp) with h1172 | h1172
                                            · linarith only [h1136, h1172, hlam]
                                            · linarith only [h1172, h853, hlam]
                                          · linarith only [h1171, h8, hlam]
                                      · linarith only [h1, h1168, hlam]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h8, h853, hc12, hc23, hlam, hphi, p1144_1]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h0, h1142, h3, h8, h853, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1144_1]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h5, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1136, h1138, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1144_1]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1136, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1142, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h6, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h0, h1137, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1144_1]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1137, hlam, p1144_0]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [h1137, h8, h853, hc12, hc25, hlam, hphi, p1144_1]
                                    · have p1144_0 := h1144c.1
                                      have p1144_1 := h1144c.2.1
                                      have p1144_2 := h1144c.2.2.1
                                      have p1144_3 := h1144c.2.2.2
                                      linarith only [hlam, p1144_0]
                              · linarith only [h0, h1136, h1137, h3, h6, h8, h853, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1191 | h1191
                              · linarith only [h0, h1136, h1191, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1193 | h1193
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1194 | h1194
                                  · rcases h3bigk with h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h1075, h1136, h1193, h5, h853, hlam, p1195_2]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      rcases p1195_3 (m.d 0 3) (by simp) with h1198 | h1198
                                      · rcases p1195_3 (m.d 1 3) (by simp) with h1199 | h1199
                                        · linarith only [h1, h1199, hlam]
                                        · rcases p1195_3 (m.d 2 3) (by simp) with h1201 | h1201
                                          · linarith only [h1201, h3, hlam]
                                          · rcases p1195_3 (m.d 3 4) (by simp) with h1203 | h1203
                                            · linarith only [h1203, h5, hlam]
                                            · linarith only [h1136, h1203, hlam]
                                      · linarith only [h1198, h3, hlam]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h0, h1075, h1136, h1193, h3, h853, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1195_1]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h0, h1191, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h1, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h8, hlam, p1195_1]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h853, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h1073, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h3, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h1191, hc13, hc35, hlam, hphi, p1195_1]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h1136, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h1191, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h5, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      rcases p1195_3 (m.d 0 3) (by simp) with h1220 | h1220
                                      · rcases p1195_3 (m.d 1 3) (by simp) with h1221 | h1221
                                        · linarith only [h1221, hlam, p1195_0]
                                        · rcases p1195_3 (m.d 2 3) (by simp) with h1223 | h1223
                                          · linarith only [h1136, h1223, hlam]
                                          · linarith only [h1223, h8, hlam]
                                      · linarith only [h1, h1220, hlam]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h0, h3, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p1195_1, u5ehi3]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h6, hlam, p1195_0]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      rcases p1195_3 (m.d 0 3) (by simp) with h1231 | h1231
                                      · rcases p1195_3 (m.d 1 3) (by simp) with h1232 | h1232
                                        · linarith only [h1232, hlam, p1195_0]
                                        · rcases p1195_3 (m.d 2 3) (by simp) with h1234 | h1234
                                          · linarith only [h1191, h1234, hlam]
                                          · linarith only [h1234, h8, hlam]
                                      · linarith only [h1, h1231, hlam]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h8, hc12, hc35, hlam, hphi, ht23, p1195_1]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [h1194, hlam, p1195_1]
                                    · have p1195_0 := h1195c.1
                                      have p1195_1 := h1195c.2.1
                                      have p1195_2 := h1195c.2.2.1
                                      have p1195_3 := h1195c.2.2.2
                                      linarith only [hlam, p1195_0]
                                  · linarith only [h1193, h1194, h8, h853, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1242 | h1242
                                  · linarith only [h0, h1136, h1193, h1242, h3, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h1136, h1242, h8, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
              · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc25, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc15, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT3_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
              · rcases m.htr 0 1 5 (by decide) (by decide) with h13 | h13
                · linarith only [h13, hlam, p0_0]
                · linarith only [h11, h13, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h16 | h16
                · linarith only [h16, hlam, p0_0]
                · linarith only [h11, h16, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 1 5 (by decide) (by decide) with h20 | h20
                · linarith only [h20, hlam, p0_0]
                · linarith only [h19, h20, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h23 | h23
                · linarith only [h23, hlam, p0_0]
                · linarith only [h10, h23, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
              · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
                · linarith only [h28, hlam, p0_0]
                · linarith only [h26, h27, h28, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
                · linarith only [h31, hlam, p0_0]
                · linarith only [h26, h31, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                · linarith only [h35, hlam, p0_0]
                · linarith only [h34, h35, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
                · linarith only [h38, hlam, p0_0]
                · linarith only [h38, h9, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h41 | h41
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 1 5 (by decide) (by decide) with h44 | h44
                · linarith only [h44, hlam, p0_0]
                · linarith only [h42, h44, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h47 | h47
                · linarith only [h47, hlam, p0_0]
                · linarith only [h42, h47, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h50 | h50
              · rcases m.htr 0 1 5 (by decide) (by decide) with h51 | h51
                · linarith only [h51, hlam, p0_0]
                · linarith only [h50, h51, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h54 | h54
                · linarith only [h54, hlam, p0_0]
                · linarith only [h41, h54, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
              · rcases m.htr 0 1 5 (by decide) (by decide) with h59 | h59
                · linarith only [h59, hlam, p0_0]
                · linarith only [h57, h59, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h62 | h62
                · linarith only [h62, hlam, p0_0]
                · linarith only [h57, h62, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 1 5 (by decide) (by decide) with h66 | h66
                · linarith only [h66, hlam, p0_0]
                · linarith only [h65, h66, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h69 | h69
                · linarith only [h69, hlam, p0_0]
                · linarith only [h69, hc01, hc15, hlam, hphi, p0_1]
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
    rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
    · linarith only [h74, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h76 | h76
      · rcases p0_3 (m.d 2 5) (by simp) with h77 | h77
        · linarith only [h77, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · rcases m.htr 0 1 2 (by decide) (by decide) with h81 | h81
              · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
                · linarith only [h82, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h82, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h85 | h85
                · linarith only [h74, h85, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h80, h85, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
              · rcases m.htr 0 1 5 (by decide) (by decide) with h89 | h89
                · linarith only [h74, h89, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h89, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
                · linarith only [h74, h88, h92, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h74, h79, h92, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · rcases m.htr 0 1 2 (by decide) (by decide) with h96 | h96
              · rcases m.htr 0 1 5 (by decide) (by decide) with h97 | h97
                · linarith only [h74, h97, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h74, h97, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h100, h74, h95, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h104, h74, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
                · linarith only [h103, h107, h74, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h107, h74, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h76, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h111 | h111
    · linarith only [h111, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h113 | h113
      · rcases p0_3 (m.d 2 5) (by simp) with h114 | h114
        · rcases p0_3 (m.d 3 5) (by simp) with h115 | h115
          · linarith only [h115, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · rcases m.htr 0 1 5 (by decide) (by decide) with h119 | h119
                · linarith only [h119, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h118, h119, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h122 | h122
                · linarith only [h111, h122, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h117, h122, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h125 | h125
              · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
                · linarith only [h111, h126, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h114, h125, h126, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h129 | h129
                · linarith only [h111, h125, h129, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h111, h114, h129, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · rcases m.htr 0 1 2 (by decide) (by decide) with h135 | h135
              · rcases m.htr 0 1 5 (by decide) (by decide) with h136 | h136
                · linarith only [h111, h136, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h135, h136, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
                · linarith only [h111, h135, h139, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h111, h134, h139, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h142 | h142
              · rcases m.htr 0 1 5 (by decide) (by decide) with h143 | h143
                · linarith only [h111, h143, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h111, h143, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h146 | h146
                · linarith only [h111, h142, h146, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h111, h146, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h113, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h150 | h150
    · linarith only [h150, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h152 | h152
      · rcases p0_3 (m.d 2 5) (by simp) with h153 | h153
        · rcases p0_3 (m.d 3 5) (by simp) with h154 | h154
          · rcases p0_3 (m.d 4 5) (by simp) with h155 | h155
            · linarith only [h155, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h157 | h157
              · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
                · linarith only [h158, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h158, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h161 | h161
                · linarith only [h150, h157, h161, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h150, h154, h161, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · linarith only [h164, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 1 5 (by decide) (by decide) with h167 | h167
                · linarith only [h150, h167, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h153, h167, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h170 | h170
                · linarith only [h150, h170, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h153, h170, hc01, hc25, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 5) (by simp) with h173 | h173
          · rcases p0_3 (m.d 4 5) (by simp) with h174 | h174
            · linarith only [h174, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h176 | h176
              · rcases m.htr 0 1 5 (by decide) (by decide) with h177 | h177
                · linarith only [h150, h177, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h177, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h180 | h180
                · linarith only [h150, h180, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h173, h180, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h183 | h183
            · linarith only [h183, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h185 | h185
              · rcases m.htr 0 1 5 (by decide) (by decide) with h186 | h186
                · linarith only [h150, h186, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h186, hc01, hc15, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h189 | h189
                · linarith only [h150, h189, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h150, h189, hc01, hc15, hlam, hphi, p0_1]
      · linarith only [h152, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h193 | h193
    · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h195 | h195
      · rcases p0_3 (m.d 2 5) (by simp) with h196 | h196
        · rcases p0_3 (m.d 3 5) (by simp) with h197 | h197
          · rcases p0_3 (m.d 4 5) (by simp) with h198 | h198
            · rcases m.htr 0 1 2 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
                · linarith only [h195, h200, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h199, h200, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h203 | h203
                · linarith only [h195, h203, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h203, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 1 5 (by decide) (by decide) with h207 | h207
                · linarith only [h195, h207, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h207, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
                · linarith only [h195, h210, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h210, hc01, hc25, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h213 | h213
            · rcases m.htr 0 1 2 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 1 5 (by decide) (by decide) with h215 | h215
                · linarith only [h195, h215, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h215, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h218 | h218
                · linarith only [h195, h218, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h218, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h221 | h221
              · rcases m.htr 0 1 5 (by decide) (by decide) with h222 | h222
                · linarith only [h195, h222, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h222, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h225 | h225
                · linarith only [h195, h221, h225, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h225, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h196, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h229 | h229
        · rcases p0_3 (m.d 3 5) (by simp) with h230 | h230
          · rcases p0_3 (m.d 4 5) (by simp) with h231 | h231
            · rcases m.htr 0 1 2 (by decide) (by decide) with h232 | h232
              · rcases m.htr 0 1 5 (by decide) (by decide) with h233 | h233
                · rcases m.htr 0 2 3 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
                    · linarith only [h235, hlam, p0_0]
                    · linarith only [h231, h235, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h238, hlam, p0_0]
                    · linarith only [h231, h232, h238, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h233, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h242 | h242
                · rcases m.htr 0 2 3 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h244 | h244
                    · linarith only [h244, hlam, p0_0]
                    · linarith only [h231, h232, h244, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h247 | h247
                    · linarith only [h247, hlam, p0_0]
                    · linarith only [h231, h232, h242, h247, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h195, h242, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 1 5 (by decide) (by decide) with h252 | h252
                · rcases m.htr 0 2 3 (by decide) (by decide) with h253 | h253
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
                    · linarith only [h254, hlam, p0_0]
                    · linarith only [h253, h254, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h257 | h257
                    · linarith only [h257, hlam, p0_0]
                    · linarith only [h230, h251, h257, hc12, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h195, h252, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h261 | h261
                · rcases m.htr 0 2 3 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h263 | h263
                    · linarith only [h263, hlam, p0_0]
                    · linarith only [h230, h262, h263, hc23, hc35, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h266 | h266
                    · linarith only [h266, hlam, p0_0]
                    · linarith only [h230, h266, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h195, h261, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h270 | h270
            · rcases m.htr 0 1 2 (by decide) (by decide) with h271 | h271
              · rcases m.htr 0 1 5 (by decide) (by decide) with h272 | h272
                · rcases m.htr 0 2 3 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
                    · linarith only [h274, hlam, p0_0]
                    · linarith only [h270, h274, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h277 | h277
                    · linarith only [h277, hlam, p0_0]
                    · linarith only [h270, h271, h277, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h195, h272, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h281 | h281
                · rcases m.htr 0 2 3 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h283 | h283
                    · linarith only [h283, hlam, p0_0]
                    · linarith only [h270, h271, h283, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
                    · linarith only [h286, hlam, p0_0]
                    · linarith only [h270, h271, h281, h286, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h195, h281, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
              · rcases m.htr 0 1 5 (by decide) (by decide) with h291 | h291
                · rcases m.htr 0 2 3 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h293 | h293
                    · linarith only [h293, hlam, p0_0]
                    · linarith only [h292, h293, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h296 | h296
                    · linarith only [h296, hlam, p0_0]
                    · linarith only [h290, h296, hc12, hc25, hlam, hphi, p0_1]
                · linarith only [h195, h291, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h300 | h300
                · rcases m.htr 0 2 3 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h302 | h302
                    · linarith only [h302, hlam, p0_0]
                    · linarith only [h290, h302, hc01, hc25, hlam, hphi, ht12, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h305 | h305
                    · linarith only [h305, hlam, p0_0]
                    · linarith only [h290, h300, h305, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                · linarith only [h195, h300, hlam]
        · linarith only [h229, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h310 | h310
    · linarith only [h310, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h312 | h312
      · linarith only [h312, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h314 | h314
        · rcases p0_3 (m.d 3 5) (by simp) with h315 | h315
          · rcases p0_3 (m.d 4 5) (by simp) with h316 | h316
            · rcases m.htr 0 1 2 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 5 (by decide) (by decide) with h318 | h318
                · linarith only [h310, h318, hlam]
                · linarith only [h316, h317, h318, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h321 | h321
                · linarith only [h310, h321, hlam]
                · linarith only [h316, h321, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h324 | h324
              · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
                · linarith only [h310, h325, hlam]
                · linarith only [h324, h325, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h328 | h328
                · linarith only [h310, h328, hlam]
                · linarith only [h315, h328, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h331 | h331
            · rcases m.htr 0 1 2 (by decide) (by decide) with h332 | h332
              · rcases m.htr 0 1 5 (by decide) (by decide) with h333 | h333
                · linarith only [h310, h333, hlam]
                · linarith only [h331, h333, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h336 | h336
                · linarith only [h310, h336, hlam]
                · linarith only [h331, h336, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h339 | h339
              · rcases m.htr 0 1 5 (by decide) (by decide) with h340 | h340
                · linarith only [h310, h340, hlam]
                · linarith only [h339, h340, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h343 | h343
                · linarith only [h310, h343, hlam]
                · linarith only [h343, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h314, hlam, p0_0]
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
    · linarith only [h348, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h350 | h350
      · rcases p0_3 (m.d 2 5) (by simp) with h351 | h351
        · rcases p0_3 (m.d 3 5) (by simp) with h352 | h352
          · linarith only [h352, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h354 | h354
            · rcases m.htr 0 1 2 (by decide) (by decide) with h355 | h355
              · rcases m.htr 0 1 5 (by decide) (by decide) with h356 | h356
                · linarith only [h350, h356, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h356, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h359 | h359
                · linarith only [h348, h350, h359, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h350, h359, hc01, hc15, hlam, hphi, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h362 | h362
              · rcases m.htr 0 1 5 (by decide) (by decide) with h363 | h363
                · linarith only [h348, h350, h363, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h363, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h366 | h366
                · linarith only [h348, h350, h366, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h348, h366, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h351, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h370 | h370
        · rcases p0_3 (m.d 3 5) (by simp) with h371 | h371
          · linarith only [h371, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h373 | h373
            · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 1 5 (by decide) (by decide) with h375 | h375
                · rcases m.htr 0 2 3 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h377 | h377
                    · linarith only [h348, h375, h377, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h377, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h380 | h380
                    · linarith only [h348, h375, h380, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h380, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h350, h373, h375, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h384 | h384
                · rcases m.htr 0 2 3 (by decide) (by decide) with h385 | h385
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h386 | h386
                    · linarith only [h348, h384, h386, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h386, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h389 | h389
                    · linarith only [h348, h384, h389, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h373, h389, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h350, h373, h384, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h393 | h393
              · rcases m.htr 0 1 5 (by decide) (by decide) with h394 | h394
                · rcases m.htr 0 2 3 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h396 | h396
                    · linarith only [h348, h396, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h396, hc02, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h399 | h399
                    · linarith only [h348, h395, h399, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h348, h399, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h350, h394, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h403 | h403
                · rcases m.htr 0 2 3 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h405 | h405
                    · linarith only [h348, h405, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h348, h405, hc02, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h408 | h408
                    · linarith only [h348, h404, h408, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h348, h408, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h350, h403, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h370, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h413 | h413
    · linarith only [h413, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h415 | h415
      · rcases p0_3 (m.d 2 5) (by simp) with h416 | h416
        · rcases p0_3 (m.d 3 5) (by simp) with h417 | h417
          · rcases p0_3 (m.d 4 5) (by simp) with h418 | h418
            · linarith only [h418, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h420 | h420
              · rcases m.htr 0 1 5 (by decide) (by decide) with h421 | h421
                · linarith only [h415, h421, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h421, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h424 | h424
                · linarith only [h413, h415, h424, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h424, hc01, hc25, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h427 | h427
            · linarith only [h427, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h429 | h429
              · rcases m.htr 0 1 5 (by decide) (by decide) with h430 | h430
                · linarith only [h413, h415, h430, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h430, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h433 | h433
                · linarith only [h413, h415, h433, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h413, h433, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h416, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h437 | h437
        · rcases p0_3 (m.d 3 5) (by simp) with h438 | h438
          · rcases p0_3 (m.d 4 5) (by simp) with h439 | h439
            · linarith only [h439, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h441 | h441
              · rcases m.htr 0 1 5 (by decide) (by decide) with h442 | h442
                · rcases m.htr 0 2 3 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h444 | h444
                    · linarith only [h413, h441, h444, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h413, h438, h444, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h447 | h447
                    · linarith only [h413, h443, h447, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h413, h438, h447, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h415, h438, h442, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h451 | h451
                · rcases m.htr 0 2 3 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h453 | h453
                    · linarith only [h413, h453, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h438, h453, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h456 | h456
                    · linarith only [h413, h452, h456, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h413, h438, h456, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h415, h438, h451, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h460 | h460
            · linarith only [h460, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h462 | h462
              · rcases m.htr 0 1 5 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 2 3 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h465 | h465
                    · linarith only [h413, h465, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h464, h465, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h468 | h468
                    · linarith only [h413, h464, h468, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h413, h468, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h415, h463, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h472 | h472
                · rcases m.htr 0 2 3 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
                    · linarith only [h413, h474, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h413, h474, hc02, hc25, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h477 | h477
                    · linarith only [h413, h473, h477, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h413, h477, hc02, hc25, hlam, hphi, p0_1]
                · linarith only [h415, h472, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h437, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h482 | h482
    · linarith only [h482, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h484 | h484
      · rcases p0_3 (m.d 2 5) (by simp) with h485 | h485
        · rcases p0_3 (m.d 3 5) (by simp) with h486 | h486
          · rcases p0_3 (m.d 4 5) (by simp) with h487 | h487
            · rcases m.htr 0 1 2 (by decide) (by decide) with h488 | h488
              · rcases m.htr 0 1 5 (by decide) (by decide) with h489 | h489
                · linarith only [h484, h489, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h489, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h492 | h492
                · linarith only [h484, h492, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h492, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h495 | h495
              · rcases m.htr 0 1 5 (by decide) (by decide) with h496 | h496
                · linarith only [h484, h496, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h496, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h499 | h499
                · linarith only [h484, h499, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h499, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h486, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h503 | h503
          · rcases p0_3 (m.d 4 5) (by simp) with h504 | h504
            · rcases m.htr 0 1 2 (by decide) (by decide) with h505 | h505
              · rcases m.htr 0 1 5 (by decide) (by decide) with h506 | h506
                · linarith only [h484, h506, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h506, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h509 | h509
                · linarith only [h484, h509, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h509, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h512 | h512
              · rcases m.htr 0 1 5 (by decide) (by decide) with h513 | h513
                · linarith only [h484, h513, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h513, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h516 | h516
                · linarith only [h484, h512, h516, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h516, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h503, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h520 | h520
        · rcases p0_3 (m.d 3 5) (by simp) with h521 | h521
          · rcases p0_3 (m.d 4 5) (by simp) with h522 | h522
            · rcases m.htr 0 1 2 (by decide) (by decide) with h523 | h523
              · rcases m.htr 0 1 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 0 2 3 (by decide) (by decide) with h525 | h525
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h526 | h526
                    · linarith only [h520, h526, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h522, h526, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h529 | h529
                    · linarith only [h520, h524, h529, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h522, h529, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h484, h524, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h533 | h533
                · rcases m.htr 0 2 3 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h535 | h535
                    · linarith only [h520, h533, h535, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h522, h535, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h538 | h538
                    · linarith only [h520, h533, h538, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h522, h538, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h484, h533, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h542 | h542
              · rcases m.htr 0 1 5 (by decide) (by decide) with h543 | h543
                · rcases m.htr 0 2 3 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h545 | h545
                    · linarith only [h520, h543, h545, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h545, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h548 | h548
                    · linarith only [h520, h548, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h548, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h484, h543, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h552 | h552
                · rcases m.htr 0 2 3 (by decide) (by decide) with h553 | h553
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h554 | h554
                    · linarith only [h520, h554, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h553, h554, hc23, hc35, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h557 | h557
                    · linarith only [h520, h557, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h557, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h484, h552, hlam]
          · linarith only [h521, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h562 | h562
          · rcases p0_3 (m.d 4 5) (by simp) with h563 | h563
            · rcases m.htr 0 1 2 (by decide) (by decide) with h564 | h564
              · rcases m.htr 0 1 5 (by decide) (by decide) with h565 | h565
                · rcases m.htr 0 2 3 (by decide) (by decide) with h566 | h566
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h567 | h567
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h568 | h568
                      · linarith only [h568, hlam, p0_0]
                      · linarith only [h563, h568, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h520, h567, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h572 | h572
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h573 | h573
                      · linarith only [h573, hlam, p0_0]
                      · linarith only [h563, h566, h573, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h520, h572, hlam]
                · linarith only [h484, h565, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h578 | h578
                · rcases m.htr 0 2 3 (by decide) (by decide) with h579 | h579
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h580 | h580
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h581 | h581
                      · linarith only [h581, hlam, p0_0]
                      · linarith only [h563, h581, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h520, h580, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h585 | h585
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h586 | h586
                      · linarith only [h586, hlam, p0_0]
                      · linarith only [h563, h564, h579, h586, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                    · linarith only [h520, h585, hlam]
                · linarith only [h484, h578, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h591 | h591
              · rcases m.htr 0 1 5 (by decide) (by decide) with h592 | h592
                · rcases m.htr 0 2 3 (by decide) (by decide) with h593 | h593
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h594 | h594
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h595 | h595
                      · linarith only [h595, hlam, p0_0]
                      · linarith only [h593, h595, hc23, hc35, hlam, hphi, p0_1]
                    · linarith only [h520, h594, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h599 | h599
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h600 | h600
                      · linarith only [h600, hlam, p0_0]
                      · linarith only [h593, h600, hc02, hc35, hlam, hphi, ht23, p0_1]
                    · linarith only [h520, h599, hlam]
                · linarith only [h484, h592, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h605 | h605
                · rcases m.htr 0 2 3 (by decide) (by decide) with h606 | h606
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h607 | h607
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h608 | h608
                      · linarith only [h608, hlam, p0_0]
                      · linarith only [h606, h608, hc23, hc35, hlam, hphi, p0_1]
                    · linarith only [h520, h607, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h612 | h612
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h613 | h613
                      · linarith only [h613, hlam, p0_0]
                      · linarith only [h591, h606, h613, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                    · linarith only [h520, h612, hlam]
                · linarith only [h484, h605, hlam]
          · linarith only [h562, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h619 | h619
    · linarith only [h619, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h621 | h621
      · linarith only [h621, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h623 | h623
        · rcases p0_3 (m.d 3 5) (by simp) with h624 | h624
          · rcases p0_3 (m.d 4 5) (by simp) with h625 | h625
            · rcases m.htr 0 1 2 (by decide) (by decide) with h626 | h626
              · rcases m.htr 0 1 5 (by decide) (by decide) with h627 | h627
                · linarith only [h619, h627, hlam]
                · linarith only [h625, h627, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h630 | h630
                · linarith only [h619, h630, hlam]
                · linarith only [h625, h630, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h633 | h633
              · rcases m.htr 0 1 5 (by decide) (by decide) with h634 | h634
                · linarith only [h619, h634, hlam]
                · linarith only [h623, h633, h634, hc12, hc25, hlam, hphi, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h637 | h637
                · linarith only [h619, h637, hlam]
                · linarith only [h637, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h624, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h641 | h641
          · rcases p0_3 (m.d 4 5) (by simp) with h642 | h642
            · rcases m.htr 0 1 2 (by decide) (by decide) with h643 | h643
              · rcases m.htr 0 1 5 (by decide) (by decide) with h644 | h644
                · linarith only [h619, h644, hlam]
                · linarith only [h642, h643, h644, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h647 | h647
                · linarith only [h619, h647, hlam]
                · linarith only [h642, h647, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h650 | h650
              · rcases m.htr 0 1 5 (by decide) (by decide) with h651 | h651
                · linarith only [h619, h651, hlam]
                · linarith only [h650, h651, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h654 | h654
                · linarith only [h619, h654, hlam]
                · linarith only [h654, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h641, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h658 | h658
    · linarith only [h658, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h660 | h660
      · rcases p0_3 (m.d 2 5) (by simp) with h661 | h661
        · linarith only [h661, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h663 | h663
          · rcases p0_3 (m.d 4 5) (by simp) with h664 | h664
            · rcases m.htr 0 1 2 (by decide) (by decide) with h665 | h665
              · rcases m.htr 0 1 5 (by decide) (by decide) with h666 | h666
                · linarith only [h660, h666, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h658, h666, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h669 | h669
                · linarith only [h658, h660, h669, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h658, h669, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h672 | h672
              · rcases m.htr 0 1 5 (by decide) (by decide) with h673 | h673
                · linarith only [h658, h660, h673, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h658, h673, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h676 | h676
                · linarith only [h658, h660, h676, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h658, h676, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h663, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h680 | h680
        · linarith only [h680, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h682 | h682
          · rcases p0_3 (m.d 4 5) (by simp) with h683 | h683
            · rcases m.htr 0 1 2 (by decide) (by decide) with h684 | h684
              · rcases m.htr 0 1 5 (by decide) (by decide) with h685 | h685
                · rcases m.htr 0 2 3 (by decide) (by decide) with h686 | h686
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h687 | h687
                    · linarith only [h658, h687, hlam]
                    · linarith only [h683, h687, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h690 | h690
                    · linarith only [h658, h690, hlam]
                    · linarith only [h683, h690, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h660, h683, h684, h685, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h694 | h694
                · rcases m.htr 0 2 3 (by decide) (by decide) with h695 | h695
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h696 | h696
                    · linarith only [h658, h696, hlam]
                    · linarith only [h683, h695, h696, hc23, hc45, hlam, hphi, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h699 | h699
                    · linarith only [h658, h699, hlam]
                    · linarith only [h683, h699, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h660, h683, h694, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h703 | h703
              · rcases m.htr 0 1 5 (by decide) (by decide) with h704 | h704
                · rcases m.htr 0 2 3 (by decide) (by decide) with h705 | h705
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h706 | h706
                    · linarith only [h658, h706, hlam]
                    · linarith only [h705, h706, hc23, hc35, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h709 | h709
                    · linarith only [h658, h709, hlam]
                    · linarith only [h709, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h660, h703, h704, hc12, hc35, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h713 | h713
                · rcases m.htr 0 2 3 (by decide) (by decide) with h714 | h714
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h715 | h715
                    · linarith only [h658, h715, hlam]
                    · linarith only [h703, h715, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h718 | h718
                    · linarith only [h658, h718, hlam]
                    · linarith only [h703, h713, h718, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                · linarith only [h660, h713, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h682, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h724 | h724
    · linarith only [h724, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h726 | h726
      · rcases p0_3 (m.d 2 5) (by simp) with h727 | h727
        · rcases p0_3 (m.d 3 5) (by simp) with h728 | h728
          · rcases p0_3 (m.d 4 5) (by simp) with h729 | h729
            · linarith only [h729, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h731 | h731
              · rcases m.htr 0 1 5 (by decide) (by decide) with h732 | h732
                · linarith only [h726, h732, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h724, h727, h732, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h735 | h735
                · linarith only [h724, h726, h735, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h724, h735, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h728, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h739 | h739
          · rcases p0_3 (m.d 4 5) (by simp) with h740 | h740
            · linarith only [h740, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h742 | h742
              · rcases m.htr 0 1 5 (by decide) (by decide) with h743 | h743
                · linarith only [h724, h726, h743, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h724, h743, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h746 | h746
                · linarith only [h724, h726, h746, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h724, h746, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h739, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h750 | h750
        · rcases p0_3 (m.d 3 5) (by simp) with h751 | h751
          · rcases p0_3 (m.d 4 5) (by simp) with h752 | h752
            · linarith only [h752, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h754 | h754
              · rcases m.htr 0 1 5 (by decide) (by decide) with h755 | h755
                · rcases m.htr 0 2 3 (by decide) (by decide) with h756 | h756
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h757 | h757
                    · linarith only [h724, h750, h754, h757, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h724, h756, h757, hc23, hc35, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h760 | h760
                    · linarith only [h724, h750, h760, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h724, h760, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h726, h755, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h764 | h764
                · rcases m.htr 0 2 3 (by decide) (by decide) with h765 | h765
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h766 | h766
                    · linarith only [h724, h750, h766, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h724, h766, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h769 | h769
                    · linarith only [h724, h750, h765, h769, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h724, h769, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h726, h764, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h751, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h774 | h774
          · rcases p0_3 (m.d 4 5) (by simp) with h775 | h775
            · linarith only [h775, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h777 | h777
              · rcases m.htr 0 1 5 (by decide) (by decide) with h778 | h778
                · rcases m.htr 0 2 3 (by decide) (by decide) with h779 | h779
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h780 | h780
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h781 | h781
                      · linarith only [h724, h779, h781, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                      · linarith only [h724, h781, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h750, h780, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h785 | h785
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
                      · linarith only [h724, h786, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h724, h786, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h750, h777, h785, hc12, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h726, h778, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h791 | h791
                · rcases m.htr 0 2 3 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h793 | h793
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h794 | h794
                      · linarith only [h724, h794, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h724, h794, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h750, h792, h793, hc23, hc35, hlam, hphi, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h798 | h798
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h799 | h799
                      · linarith only [h724, h799, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h724, h799, hc03, hc35, hlam, hphi, p0_1]
                    · linarith only [h750, h798, hc02, hc35, hlam, hphi, ht23, p0_1]
                · linarith only [h726, h791, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h774, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h805 | h805
    · linarith only [h805, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h807 | h807
      · rcases p0_3 (m.d 2 5) (by simp) with h808 | h808
        · rcases p0_3 (m.d 3 5) (by simp) with h809 | h809
          · rcases p0_3 (m.d 4 5) (by simp) with h810 | h810
            · rcases m.htr 0 1 2 (by decide) (by decide) with h811 | h811
              · rcases m.htr 0 1 5 (by decide) (by decide) with h812 | h812
                · linarith only [h807, h812, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h808, h812, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h815 | h815
                · linarith only [h807, h815, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h815, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h810, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h819 | h819
            · rcases m.htr 0 1 2 (by decide) (by decide) with h820 | h820
              · rcases m.htr 0 1 5 (by decide) (by decide) with h821 | h821
                · linarith only [h807, h821, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h821, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h824 | h824
                · linarith only [h807, h824, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h824, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h819, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h828 | h828
          · rcases p0_3 (m.d 4 5) (by simp) with h829 | h829
            · rcases m.htr 0 1 2 (by decide) (by decide) with h830 | h830
              · rcases m.htr 0 1 5 (by decide) (by decide) with h831 | h831
                · linarith only [h807, h831, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h828, h831, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h834 | h834
                · linarith only [h807, h834, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h834, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h829, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h838 | h838
            · rcases m.htr 0 1 2 (by decide) (by decide) with h839 | h839
              · rcases m.htr 0 1 5 (by decide) (by decide) with h840 | h840
                · linarith only [h807, h840, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h840, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h843 | h843
                · linarith only [h807, h843, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h843, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h838, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h847 | h847
        · rcases p0_3 (m.d 3 5) (by simp) with h848 | h848
          · rcases p0_3 (m.d 4 5) (by simp) with h849 | h849
            · rcases m.htr 0 1 2 (by decide) (by decide) with h850 | h850
              · rcases m.htr 0 1 5 (by decide) (by decide) with h851 | h851
                · rcases m.htr 0 2 3 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h853 | h853
                    · linarith only [h847, h850, h851, h853, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h848, h853, hc02, hc35, hlam, hphi, ht23, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h856 | h856
                    · linarith only [h847, h856, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h856, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h807, h851, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h860 | h860
                · rcases m.htr 0 2 3 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h862 | h862
                    · linarith only [h847, h862, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h862, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h865 | h865
                    · linarith only [h847, h861, h865, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                    · linarith only [h865, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h807, h860, hlam]
            · linarith only [h849, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h870 | h870
            · rcases m.htr 0 1 2 (by decide) (by decide) with h871 | h871
              · rcases m.htr 0 1 5 (by decide) (by decide) with h872 | h872
                · rcases m.htr 0 2 3 (by decide) (by decide) with h873 | h873
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h874 | h874
                    · linarith only [h847, h874, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h874, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h877 | h877
                    · linarith only [h847, h872, h877, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h877, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h807, h872, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h881 | h881
                · rcases m.htr 0 2 3 (by decide) (by decide) with h882 | h882
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h883 | h883
                    · linarith only [h847, h881, h883, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h883, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h886 | h886
                    · linarith only [h847, h881, h886, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h886, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h807, h881, hlam]
            · linarith only [h870, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h891 | h891
          · rcases p0_3 (m.d 4 5) (by simp) with h892 | h892
            · rcases m.htr 0 1 2 (by decide) (by decide) with h893 | h893
              · rcases m.htr 0 1 5 (by decide) (by decide) with h894 | h894
                · rcases m.htr 0 2 3 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h897 | h897
                      · linarith only [h891, h894, h895, h897, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                      · linarith only [h897, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h847, h896, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h902 | h902
                      · linarith only [h891, h894, h902, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h895, h902, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h847, h901, hlam]
                · linarith only [h807, h894, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h907 | h907
                · rcases m.htr 0 2 3 (by decide) (by decide) with h908 | h908
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h909 | h909
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h910 | h910
                      · linarith only [h891, h907, h910, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h910, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h847, h909, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h914 | h914
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h915 | h915
                      · linarith only [h891, h907, h915, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                      · linarith only [h915, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h847, h914, hlam]
                · linarith only [h807, h907, hlam]
            · linarith only [h892, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h921 | h921
            · rcases m.htr 0 1 2 (by decide) (by decide) with h922 | h922
              · rcases m.htr 0 1 5 (by decide) (by decide) with h923 | h923
                · rcases m.htr 0 2 3 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h925 | h925
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h926 | h926
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h927 | h927
                        · linarith only [h927, hlam, p0_0]
                        · linarith only [h927, hc04, hc45, hlam, hphi, p0_1]
                      · linarith only [h891, h926, hlam]
                    · linarith only [h847, h925, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h932 | h932
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h933 | h933
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h934 | h934
                        · linarith only [h934, hlam, p0_0]
                        · linarith only [h934, hc04, hc45, hlam, hphi, p0_1]
                      · linarith only [h891, h933, hlam]
                    · linarith only [h847, h932, hlam]
                · linarith only [h807, h923, hlam]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h940 | h940
                · rcases m.htr 0 2 3 (by decide) (by decide) with h941 | h941
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h942 | h942
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h943 | h943
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h944 | h944
                        · linarith only [h944, hlam, p0_0]
                        · linarith only [h944, hc04, hc45, hlam, hphi, p0_1]
                      · linarith only [h891, h943, hlam]
                    · linarith only [h847, h942, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h949 | h949
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h950 | h950
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h951 | h951
                        · linarith only [h951, hlam, p0_0]
                        · linarith only [h951, hc04, hc45, hlam, hphi, p0_1]
                      · linarith only [h891, h950, hlam]
                    · linarith only [h847, h949, hlam]
                · linarith only [h807, h940, hlam]
            · linarith only [h921, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h958 | h958
    · linarith only [h958, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h960 | h960
      · linarith only [h960, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h962 | h962
        · rcases p0_3 (m.d 3 5) (by simp) with h963 | h963
          · rcases p0_3 (m.d 4 5) (by simp) with h964 | h964
            · rcases m.htr 0 1 2 (by decide) (by decide) with h965 | h965
              · rcases m.htr 0 1 5 (by decide) (by decide) with h966 | h966
                · linarith only [h958, h966, hlam]
                · linarith only [h966, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h969 | h969
                · linarith only [h958, h969, hlam]
                · linarith only [h969, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h964, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h973 | h973
            · rcases m.htr 0 1 2 (by decide) (by decide) with h974 | h974
              · rcases m.htr 0 1 5 (by decide) (by decide) with h975 | h975
                · linarith only [h958, h975, hlam]
                · linarith only [h975, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h978 | h978
                · linarith only [h958, h978, hlam]
                · linarith only [h978, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h973, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h982 | h982
          · rcases p0_3 (m.d 4 5) (by simp) with h983 | h983
            · rcases m.htr 0 1 2 (by decide) (by decide) with h984 | h984
              · rcases m.htr 0 1 5 (by decide) (by decide) with h985 | h985
                · linarith only [h958, h985, hlam]
                · linarith only [h985, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h988 | h988
                · linarith only [h958, h988, hlam]
                · linarith only [h988, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h983, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h992 | h992
            · rcases m.htr 0 1 2 (by decide) (by decide) with h993 | h993
              · rcases m.htr 0 1 5 (by decide) (by decide) with h994 | h994
                · linarith only [h958, h994, hlam]
                · linarith only [h993, h994, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h997 | h997
                · linarith only [h958, h997, hlam]
                · linarith only [h997, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h992, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1001 | h1001
    · linarith only [h1001, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1003 | h1003
      · rcases p0_3 (m.d 2 5) (by simp) with h1004 | h1004
        · linarith only [h1004, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1006 | h1006
          · rcases p0_3 (m.d 4 5) (by simp) with h1007 | h1007
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1008 | h1008
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1009 | h1009
                · linarith only [h1003, h1009, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1001, h1006, h1009, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1012 | h1012
                · linarith only [h1001, h1003, h1012, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1001, h1012, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1007, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1016 | h1016
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1017 | h1017
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1018 | h1018
                · linarith only [h1001, h1003, h1018, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1001, h1018, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1021 | h1021
                · linarith only [h1001, h1003, h1021, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1001, h1021, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1016, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1025 | h1025
        · linarith only [h1025, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1027 | h1027
          · rcases p0_3 (m.d 4 5) (by simp) with h1028 | h1028
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1029 | h1029
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1030 | h1030
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1031 | h1031
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1032 | h1032
                    · linarith only [h1001, h1032, hlam]
                    · linarith only [h1031, h1032, hc23, hc45, hlam, hphi, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1035 | h1035
                    · linarith only [h1001, h1035, hlam]
                    · linarith only [h1035, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1003, h1029, h1030, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1039 | h1039
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1040 | h1040
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1041 | h1041
                    · linarith only [h1001, h1041, hlam]
                    · linarith only [h1029, h1041, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1044 | h1044
                    · linarith only [h1001, h1044, hlam]
                    · linarith only [h1027, h1029, h1039, h1044, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1]
                · linarith only [h1003, h1039, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1028, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1049 | h1049
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1050 | h1050
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1051 | h1051
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1052 | h1052
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1053 | h1053
                    · linarith only [h1001, h1053, hlam]
                    · linarith only [h1052, h1053, hc23, hc45, hlam, hphi, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1056 | h1056
                    · linarith only [h1001, h1056, hlam]
                    · linarith only [h1056, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1003, h1050, h1051, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1060 | h1060
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1061 | h1061
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1062 | h1062
                    · linarith only [h1001, h1062, hlam]
                    · linarith only [h1050, h1062, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1065 | h1065
                    · linarith only [h1001, h1065, hlam]
                    · linarith only [h1050, h1060, h1065, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h1003, h1060, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1049, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h1070 | h1070
    · linarith only [h1070, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h1072 | h1072
      · rcases p0_3 (m.d 2 5) (by simp) with h1073 | h1073
        · rcases p0_3 (m.d 3 5) (by simp) with h1074 | h1074
          · linarith only [h1074, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1076 | h1076
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1077 | h1077
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1078 | h1078
                · linarith only [h1072, h1078, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1070, h1073, h1078, hc01, hc25, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1081 | h1081
                · linarith only [h1070, h1072, h1081, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1070, h1081, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1076, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1085 | h1085
          · linarith only [h1085, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1087 | h1087
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1088 | h1088
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1089 | h1089
                · linarith only [h1070, h1072, h1089, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                · linarith only [h1070, h1089, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1092 | h1092
                · linarith only [h1070, h1072, h1088, h1092, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h1070, h1092, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1087, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h1096 | h1096
        · rcases p0_3 (m.d 3 5) (by simp) with h1097 | h1097
          · linarith only [h1097, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1099 | h1099
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1100 | h1100
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1101 | h1101
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1102 | h1102
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1103 | h1103
                    · linarith only [h1070, h1096, h1100, h1101, h1103, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
                    · linarith only [h1070, h1103, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1106 | h1106
                    · linarith only [h1070, h1096, h1101, h1106, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1070, h1106, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1072, h1101, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1110 | h1110
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1111 | h1111
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1112 | h1112
                    · linarith only [h1070, h1096, h1110, h1112, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1070, h1112, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1115 | h1115
                    · linarith only [h1070, h1096, h1110, h1115, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                    · linarith only [h1070, h1115, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1072, h1110, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1099, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h1120 | h1120
          · linarith only [h1120, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h1122 | h1122
            · rcases m.htr 0 1 2 (by decide) (by decide) with h1123 | h1123
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1124 | h1124
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1125 | h1125
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1126 | h1126
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1127 | h1127
                      · linarith only [h1070, h1127, hlam]
                      · linarith only [h1127, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1096, h1125, h1126, hc23, hc45, hlam, hphi, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1131 | h1131
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1132 | h1132
                      · linarith only [h1070, h1132, hlam]
                      · linarith only [h1125, h1132, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
                    · linarith only [h1096, h1123, h1131, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
                · linarith only [h1072, h1123, h1124, hc12, hc45, hlam, hphi, ht23, ht34, p0_1]
              · rcases m.htr 0 1 5 (by decide) (by decide) with h1137 | h1137
                · rcases m.htr 0 2 3 (by decide) (by decide) with h1138 | h1138
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1139 | h1139
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1140 | h1140
                      · linarith only [h1070, h1140, hlam]
                      · linarith only [h1140, hc03, hc45, hlam, hphi, ht34, p0_1]
                    · linarith only [h1096, h1123, h1139, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h1144 | h1144
                    · rcases m.htr 0 3 5 (by decide) (by decide) with h1145 | h1145
                      · linarith only [h1070, h1145, hlam]
                      · linarith only [h1123, h1137, h1138, h1145, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                    · linarith only [h1096, h1123, h1137, h1144, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1]
                · linarith only [h1072, h1137, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h1122, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LI_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
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
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h11, h14, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h13, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h12, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h11, h19, h4, h6, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h19, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h10, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h0, h23, h4, h9, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h23, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h8, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h7, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                        · linarith only [h1, h28, h32, h6, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                              · linarith only [h0, h1, h30, h34, h36, h6, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                                · linarith only [h0, h30, h38, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h1, h34, h38, h6, hc23, hc34, hlam, hphi]
                            · linarith only [h29, h32, h35, hc13, hlam, hphi, ht34, ht45, u5elo0]
                          · linarith only [h30, h34, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h31, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h30, h4, h44, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h44, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h29, h6, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h1, h28, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h50 | h50
            · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
              · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
                · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h4, h50, h54, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                                  · linarith only [h1, h57, h62, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h62, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h4, h61, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h4, h51, h56, h60, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h59, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h58, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h1, h51, h54, h56, h57, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h56, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h53, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h52, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
                · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                    · linarith only [h0, h4, h50, h75, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                        · linarith only [h1, h51, h78, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                                  · rcases h0bigk with h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h77, h83, h84, hc45, hlam, hphi, ht0b, ht5b, p85_1, u0elo0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h4, h77, h83, h84, hc45, hlam, hphi, ht0b, ht5b, p85_1, u0elo0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h4, h51, h77, h83, h84, hc45, hlam, hphi, ht0b, ht5b, p85_1, u0elo0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      rcases p85_3 (m.d 0 1) (by simp) with h90 | h90
                                      · rcases p85_3 (m.d 0 2) (by simp) with h91 | h91
                                        · linarith only [h0, h91, hlam]
                                        · linarith only [h50, h91, hlam]
                                      · linarith only [h3, h90, hlam]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, hlam, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h4, hlam, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h4, h51, hlam, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h4, h51, h82, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h1, hlam, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h51, h82, hc02, hc23, hlam, hphi, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h51, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h50, h51, h82, h83, h84, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h2, hlam, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h0, h77, h83, h84, hc45, hlam, hphi, ht0b, ht5b, p85_1, u0elo3]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h1, h75, h77, h83, h84, hc45, hlam, hphi, ht0b, ht5b, p85_1, u0elo3]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      rcases p85_3 (m.d 0 1) (by simp) with h109 | h109
                                      · rcases p85_3 (m.d 0 2) (by simp) with h110 | h110
                                        · linarith only [h110, h4, h51, hlam]
                                        · linarith only [h110, h50, hlam]
                                      · linarith only [h109, h3, hlam]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h3, hlam, p85_1]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h50, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h73, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [h74, hlam, p85_0]
                                    · have p85_0 := h85c.1
                                      have p85_1 := h85c.2.1
                                      have p85_2 := h85c.2.2.1
                                      have p85_3 := h85c.2.2.2
                                      linarith only [hlam, p85_0]
                                  · linarith only [h4, h51, h84, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                · linarith only [h83, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                                  · rcases h0bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h0, h121, h122, h77, hc45, hlam, hphi, ht0b, ht5b, p123_1, u0elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h0, h121, h122, h4, h77, hc45, hlam, hphi, ht0b, ht5b, p123_1, u0elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h0, h121, h122, h4, h51, h77, hc45, hlam, hphi, ht0b, ht5b, p123_1, u0elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      rcases p123_3 (m.d 0 1) (by simp) with h128 | h128
                                      · rcases p123_3 (m.d 0 2) (by simp) with h129 | h129
                                        · linarith only [h0, h129, hlam]
                                        · linarith only [h129, h50, hlam]
                                      · linarith only [h128, h3, hlam]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h0, hlam, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h4, hlam, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h4, h51, hlam, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, h4, h82, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h1, hlam, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h0, h51, h77, hc25, hlam, hphi, ht0b, ht5b, p123_1, u0elo3]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h51, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      rcases p123_3 (m.d 0 1) (by simp) with h142 | h142
                                      · rcases p123_3 (m.d 0 2) (by simp) with h143 | h143
                                        · linarith only [h143, h4, hlam]
                                        · linarith only [h143, h50, hlam]
                                      · linarith only [h142, h3, hlam]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h2, hlam, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h0, h121, h122, h2, h77, hc45, hlam, hphi, ht0b, ht5b, p123_1, u0elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h0, h121, h122, h2, h4, h77, hc45, hlam, hphi, ht0b, ht5b, p123_1, u0elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      rcases p123_3 (m.d 0 1) (by simp) with h151 | h151
                                      · rcases p123_3 (m.d 0 2) (by simp) with h152 | h152
                                        · linarith only [h152, h4, h51, hlam]
                                        · linarith only [h152, h50, hlam]
                                      · linarith only [h151, h3, hlam]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, hlam, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h50, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h73, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h74, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                  · linarith only [h122, h4, h82, hc02, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h121, h4, h77, hc25, hlam, hphi, u5elo3]
                            · linarith only [h78, h81, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h75, h77, h80, hc25, hlam, hphi, u5elo3]
                      · linarith only [h77, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h4, h50, h51, h74, hc25, hlam, hphi, u5elo4]
                · linarith only [h4, h50, h73, hc25, hlam, hphi, u5elo3]
            · linarith only [h50, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h170 | h170
        · rcases m.htr 0 2 3 (by decide) (by decide) with h171 | h171
          · rcases m.htr 0 2 5 (by decide) (by decide) with h172 | h172
            · rcases m.htr 0 3 4 (by decide) (by decide) with h173 | h173
              · linarith only [h1, h173, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 0 4 5 (by decide) (by decide) with h176 | h176
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                        · linarith only [h1, h173, h179, h2, hlam]
                        · linarith only [h0, h177, h179, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h177, h178, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                      · linarith only [h0, h171, h177, h183, h2, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h183, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h176, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h175, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h172, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h189 | h189
            · rcases m.htr 0 3 4 (by decide) (by decide) with h190 | h190
              · linarith only [h1, h190, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h192 | h192
                · rcases m.htr 0 4 5 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                    · linarith only [h0, h171, h194, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                        · linarith only [h1, h171, h190, h197, h2, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                              · linarith only [h1, h194, h196, h197, h2, h201, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                                  · rcases h0bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h0, h196, h197, h2, h203, h204, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h0, h171, h196, h197, h2, h203, h204, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h2, hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      rcases p205_3 (m.d 0 1) (by simp) with h210 | h210
                                      · rcases p205_3 (m.d 0 2) (by simp) with h211 | h211
                                        · linarith only [h0, h211, hlam]
                                        · linarith only [h189, h211, hlam]
                                      · linarith only [h170, h210, hlam]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h0, hlam, p205_1]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h171, hlam, p205_1]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h0, h171, h196, h2, h203, h204, hc45, hlam, hphi, ht0b, ht5b, p205_1, u0elo2]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h170, h171, h196, h201, h203, h204, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h1, hlam, p205_1]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h0, h1, h196, h2, h203, h204, hc45, hlam, hphi, ht0b, ht5b, p205_1, u0elo3]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h190, hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      rcases p205_3 (m.d 0 1) (by simp) with h224 | h224
                                      · rcases p205_3 (m.d 0 2) (by simp) with h225 | h225
                                        · linarith only [h171, h225, hlam]
                                        · linarith only [h189, h225, hlam]
                                      · linarith only [h170, h224, hlam]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h0, h196, h203, h204, hc45, hlam, hphi, ht0b, ht5b, p205_1, u0elo3]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h0, h196, h203, h204, hc45, hlam, hphi, ht0b, ht5b, p205_1, u0elo3]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h1, h194, h196, h203, h204, hc45, hlam, hphi, ht0b, ht5b, p205_1, u0elo3]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      rcases p205_3 (m.d 0 1) (by simp) with h233 | h233
                                      · linarith only [h2, h233, hlam]
                                      · linarith only [h170, h233, hlam]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h170, hlam, p205_1]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h189, hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h192, hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [h193, hlam, p205_0]
                                    · have p205_0 := h205c.1
                                      have p205_1 := h205c.2.1
                                      have p205_2 := h205c.2.2.1
                                      have p205_3 := h205c.2.2.2
                                      linarith only [hlam, p205_0]
                                  · linarith only [h201, h204, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h1, h171, h197, h199, h2, h203, hc02, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2, h200, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h194, h196, h199, hc25, hlam, hphi, u5elo3]
                      · linarith only [h196, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h193, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h171, h189, h192, hc25, hlam, hphi, u5elo3]
            · linarith only [h189, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h170, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h250 | h250
      · rcases m.htr 0 1 5 (by decide) (by decide) with h251 | h251
        · rcases m.htr 0 2 3 (by decide) (by decide) with h252 | h252
          · linarith only [h0, h1, h252, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
            · rcases m.htr 0 3 4 (by decide) (by decide) with h255 | h255
              · rcases m.htr 0 3 5 (by decide) (by decide) with h256 | h256
                · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                    · linarith only [h0, h252, h258, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h260 | h260
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h265 | h265
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                                  · rcases h0bigk with h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, h1, h258, h260, h265, h266, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h1, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h1, h257, h258, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      rcases p267_3 (m.d 0 1) (by simp) with h272 | h272
                                      · rcases p267_3 (m.d 0 2) (by simp) with h273 | h273
                                        · linarith only [h0, h273, hlam]
                                        · linarith only [h254, h273, hlam]
                                      · linarith only [h251, h272, hlam]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, hlam, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h252, hlam, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h250, h261, h266, hc45, hlam, hphi, ht0b, ht5b, p267_1, u0elo1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      rcases p267_3 (m.d 0 1) (by simp) with h281 | h281
                                      · rcases p267_3 (m.d 0 2) (by simp) with h282 | h282
                                        · rcases p267_3 (m.d 0 3) (by simp) with h283 | h283
                                          · rcases p267_3 (m.d 0 4) (by simp) with h284 | h284
                                            · rcases p267_3 (m.d 0 5) (by simp) with h285 | h285
                                              · linarith only [h254, h285, hlam]
                                              · rcases h3bigk with h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h1, hlam, p287_1]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h252, hlam, p287_1]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h266, hc45, hlam, hphi, ht0b, ht5b, p287_1, u0elo2]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  rcases p287_3 (m.d 0 3) (by simp) with h292 | h292
                                                  · rcases p287_3 (m.d 1 3) (by simp) with h293 | h293
                                                    · rcases p287_3 (m.d 2 3) (by simp) with h294 | h294
                                                      · rcases p287_3 (m.d 3 4) (by simp) with h295 | h295
                                                        · linarith only [h255, h295, hlam]
                                                        · linarith only [h266, h295, hlam]
                                                      · linarith only [h265, h294, hlam]
                                                    · linarith only [h262, h293, hlam]
                                                  · linarith only [h292, hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h0, h1, h258, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, p287_1]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h258, hlam, p287_1]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  rcases p287_3 (m.d 0 3) (by simp) with h304 | h304
                                                  · linarith only [h1, h304, hlam]
                                                  · linarith only [h255, h304, hlam]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h0, h1, h251, h260, h265, hlam, p267_1, p287_2]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h0, h1, h251, h260, h265, h266, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, p287_1]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h0, h1, h251, h260, h265, h266, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, p287_1]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  rcases p287_3 (m.d 0 3) (by simp) with h311 | h311
                                                  · linarith only [h252, h311, hlam]
                                                  · linarith only [h255, h311, hlam]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h251, h252, h260, h265, hlam, p267_1, p287_2]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h255, hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h261, hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h264, hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h250, h261, h266, hc45, hlam, hphi, ht0b, ht5b, p287_1, u0elo0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h256, hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h262, hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h265, hlam, p287_0]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [h266, hlam, p287_1]
                                                · have p287_0 := h287c.1
                                                  have p287_1 := h287c.2.1
                                                  have p287_2 := h287c.2.2.1
                                                  have p287_3 := h287c.2.2.2
                                                  linarith only [hlam, p287_0]
                                            · linarith only [h257, h284, hlam]
                                          · linarith only [h256, h283, hlam]
                                        · linarith only [h254, h282, hlam]
                                      · linarith only [h251, h281, hlam]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h250, hc14, hlam, hphi, ht0b, ht45, ht5b, p267_1, u0elo2]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, h260, h265, h266, hc45, hlam, hphi, ht0b, ht5b, p267_1, u0elo2]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h257, hc45, hlam, hphi, ht0b, ht5b, p267_1, u0elo2]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      rcases p267_3 (m.d 0 1) (by simp) with h333 | h333
                                      · linarith only [h1, h333, hlam]
                                      · linarith only [h251, h333, hlam]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h250, hlam, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h0, h260, h265, h266, hc45, hlam, hphi, ht0b, ht5b, p267_1, u0elo3]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h255, hlam, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      rcases p267_3 (m.d 0 1) (by simp) with h340 | h340
                                      · rcases p267_3 (m.d 0 2) (by simp) with h341 | h341
                                        · rcases p267_3 (m.d 0 3) (by simp) with h342 | h342
                                          · rcases p267_3 (m.d 0 4) (by simp) with h343 | h343
                                            · rcases p267_3 (m.d 0 5) (by simp) with h344 | h344
                                              · linarith only [h257, h344, hlam]
                                              · rcases h3bigk with h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h1, hlam, p346_1]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h252, hlam, p346_1]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h266, hc45, hlam, hphi, ht0b, ht5b, p346_1, u0elo2]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  rcases p346_3 (m.d 0 3) (by simp) with h351 | h351
                                                  · rcases p346_3 (m.d 1 3) (by simp) with h352 | h352
                                                    · rcases p346_3 (m.d 2 3) (by simp) with h353 | h353
                                                      · rcases p346_3 (m.d 3 4) (by simp) with h354 | h354
                                                        · linarith only [h255, h354, hlam]
                                                        · linarith only [h266, h354, hlam]
                                                      · linarith only [h265, h353, hlam]
                                                    · linarith only [h262, h352, hlam]
                                                  · linarith only [h351, hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h1, h250, h251, h260, h265, h266, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p267_1, p346_1]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h258, hlam, p346_1]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  rcases p346_3 (m.d 0 3) (by simp) with h363 | h363
                                                  · linarith only [h1, h363, hlam]
                                                  · linarith only [h255, h363, hlam]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h1, h250, h251, h260, h265, hlam, p267_1, p346_2]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h1, h250, h251, h260, h265, h266, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, p346_1]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h1, h250, h251, h260, h265, h266, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p267_1, p346_1]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  rcases p346_3 (m.d 0 3) (by simp) with h370 | h370
                                                  · linarith only [h252, h370, hlam]
                                                  · linarith only [h255, h370, hlam]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h251, h252, h260, h265, h341, hlam, p267_1, p346_2]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h255, hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h261, hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h264, hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h250, h261, h266, hc45, hlam, hphi, ht0b, ht5b, p346_1, u0elo0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h256, hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h262, hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h265, hlam, p346_0]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [h266, hlam, p346_1]
                                                · have p346_0 := h346c.1
                                                  have p346_1 := h346c.2.1
                                                  have p346_2 := h346c.2.2.1
                                                  have p346_3 := h346c.2.2.2
                                                  linarith only [hlam, p346_0]
                                            · linarith only [h257, h343, hlam]
                                          · linarith only [h256, h342, hlam]
                                        · linarith only [h254, h341, hlam]
                                      · linarith only [h251, h340, hlam]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h251, hlam, p267_1]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h254, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h256, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [h257, hlam, p267_0]
                                    · have p267_0 := h267c.1
                                      have p267_1 := h267c.2.1
                                      have p267_2 := h267c.2.2.1
                                      have p267_3 := h267c.2.2.2
                                      linarith only [hlam, p267_0]
                                  · linarith only [h266, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1, h258, h265, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h1, h258, h260, h264, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h263, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1, h260, h262, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1, h260, h261, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h260, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h257, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h256, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1, h250, h255, hlam]
            · linarith only [h254, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h251, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h405 | h405
        · rcases m.htr 0 2 3 (by decide) (by decide) with h406 | h406
          · linarith only [h0, h1, h406, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h408 | h408
            · rcases m.htr 0 3 4 (by decide) (by decide) with h409 | h409
              · rcases m.htr 0 3 5 (by decide) (by decide) with h410 | h410
                · rcases m.htr 0 4 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                    · linarith only [h0, h406, h412, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h414 | h414
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h415 | h415
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h416 | h416
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h417 | h417
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h420 | h420
                                  · rcases h0bigk with h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h250, h412, h414, h415, h419, h420, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h1, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h250, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      rcases p421_3 (m.d 0 1) (by simp) with h426 | h426
                                      · rcases p421_3 (m.d 0 2) (by simp) with h427 | h427
                                        · linarith only [h0, h427, hlam]
                                        · linarith only [h408, h427, hlam]
                                      · linarith only [h405, h426, hlam]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h406, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h250, h414, h419, h420, hc45, hlam, hphi, ht0b, ht5b, p421_1, u0elo1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      rcases p421_3 (m.d 0 1) (by simp) with h435 | h435
                                      · rcases p421_3 (m.d 0 2) (by simp) with h436 | h436
                                        · rcases p421_3 (m.d 0 3) (by simp) with h437 | h437
                                          · rcases p421_3 (m.d 0 4) (by simp) with h438 | h438
                                            · rcases p421_3 (m.d 0 5) (by simp) with h439 | h439
                                              · linarith only [h408, h439, hlam]
                                              · rcases h3bigk with h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h1, hlam, p441_1]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h406, hlam, p441_1]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h420, hc45, hlam, hphi, ht0b, ht5b, p441_1, u0elo2]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  rcases p441_3 (m.d 0 3) (by simp) with h446 | h446
                                                  · rcases p441_3 (m.d 1 3) (by simp) with h447 | h447
                                                    · rcases p441_3 (m.d 2 3) (by simp) with h448 | h448
                                                      · rcases p441_3 (m.d 3 4) (by simp) with h449 | h449
                                                        · linarith only [h409, h449, hlam]
                                                        · linarith only [h420, h449, hlam]
                                                      · linarith only [h419, h448, hlam]
                                                    · linarith only [h416, h447, hlam]
                                                  · linarith only [h446, hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h0, h1, h405, h412, h414, h419, h420, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p421_1, p441_1]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h412, hlam, p441_1]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  rcases p441_3 (m.d 0 3) (by simp) with h458 | h458
                                                  · linarith only [h1, h458, hlam]
                                                  · linarith only [h409, h458, hlam]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h0, h1, h405, h414, h419, hlam, p421_1, p441_2]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h0, h250, h405, h409, h414, h419, h420, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p421_1, p441_1]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h0, h250, h405, h414, h415, h419, h420, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p421_1, p441_1]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  rcases p441_3 (m.d 0 3) (by simp) with h465 | h465
                                                  · linarith only [h406, h465, hlam]
                                                  · linarith only [h409, h465, hlam]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h405, h406, h414, h419, hlam, p421_1, p441_2]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h409, hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h415, hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h418, hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h409, h420, hc45, hlam, hphi, ht0b, ht5b, p441_1, u0elo2]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h410, hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h416, hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h419, hlam, p441_0]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [h420, hlam, p441_1]
                                                · have p441_0 := h441c.1
                                                  have p441_1 := h441c.2.1
                                                  have p441_2 := h441c.2.2.1
                                                  have p441_3 := h441c.2.2.2
                                                  linarith only [hlam, p441_0]
                                            · linarith only [h411, h438, hlam]
                                          · linarith only [h410, h437, hlam]
                                        · linarith only [h408, h436, hlam]
                                      · linarith only [h405, h435, hlam]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h414, h419, h420, hc45, hlam, hphi, ht0b, ht5b, p421_1, u0elo2]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h414, h419, h420, hc45, hlam, hphi, ht0b, ht5b, p421_1, u0elo2]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h250, h414, h419, h420, hc45, hlam, hphi, ht0b, ht5b, p421_1, u0elo2]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      rcases p421_3 (m.d 0 1) (by simp) with h487 | h487
                                      · linarith only [h1, h487, hlam]
                                      · linarith only [h405, h487, hlam]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h414, h419, h420, hc45, hlam, hphi, ht0b, ht5b, p421_1, u0elo3]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h409, h414, h419, h420, hc45, hlam, hphi, ht0b, ht5b, p421_1, u0elo2]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h409, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      rcases p421_3 (m.d 0 1) (by simp) with h494 | h494
                                      · linarith only [h250, h494, hlam]
                                      · linarith only [h405, h494, hlam]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h405, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h408, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h410, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h411, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                  · linarith only [h420, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h250, h412, h415, h419, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h250, h412, h414, h415, h418, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h250, h414, h417, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h250, h414, h415, h416, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1, h409, h414, h415, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h414, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h411, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h410, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h511 | h511
                · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                    · linarith only [h0, h1, h409, h513, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                        · linarith only [h0, h1, h409, h513, h515, h516, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1, h515, h516, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h515, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1, h409, h512, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h1, h511, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h408, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h405, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h524 | h524
    · rcases m.htr 0 1 4 (by decide) (by decide) with h525 | h525
      · rcases m.htr 0 1 5 (by decide) (by decide) with h526 | h526
        · rcases m.htr 0 2 3 (by decide) (by decide) with h527 | h527
          · rcases m.htr 0 2 5 (by decide) (by decide) with h528 | h528
            · rcases m.htr 0 3 4 (by decide) (by decide) with h529 | h529
              · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
                · rcases m.htr 0 4 5 (by decide) (by decide) with h531 | h531
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h532 | h532
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h533 | h533
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h535 | h535
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h538 | h538
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h539 | h539
                                  · linarith only [h524, h532, h537, h539, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h539, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h538, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h0, h524, h534, h537, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h536, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h535, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h546 | h546
                          · linarith only [h0, h524, h529, h534, h546, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h546, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h533, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h527, h532, hlam]
                  · linarith only [h531, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h529, h530, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h553 | h553
                · rcases m.htr 0 4 5 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h555 | h555
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
                        · linarith only [h524, h529, h557, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h560 | h560
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                              · linarith only [h525, h529, h555, h557, h561, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h563 | h563
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                                  · rcases h0bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h0, hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h0, h553, h564, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p565_1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h0, h529, h553, h564, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p565_1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      rcases p565_3 (m.d 0 1) (by simp) with h570 | h570
                                      · rcases p565_3 (m.d 0 2) (by simp) with h571 | h571
                                        · rcases p565_3 (m.d 0 3) (by simp) with h572 | h572
                                          · linarith only [h524, h572, hlam]
                                          · linarith only [h553, h572, hlam]
                                        · linarith only [h528, h571, hlam]
                                      · linarith only [h526, h570, hlam]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h524, h555, h563, h564, hc45, hlam, hphi, ht0b, ht5b, p565_1, u0elo1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h524, h555, h563, h564, hc45, hlam, hphi, ht0b, ht5b, p565_1, u0elo1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h525, h555, h557, h563, h564, hc45, hlam, hphi, ht0b, ht5b, p565_1, u0elo1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      rcases p565_3 (m.d 0 1) (by simp) with h581 | h581
                                      · linarith only [h0, h581, hlam]
                                      · linarith only [h526, h581, hlam]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h524, hlam, p565_1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h527, hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h529, hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      rcases p565_3 (m.d 0 1) (by simp) with h588 | h588
                                      · rcases p565_3 (m.d 0 2) (by simp) with h589 | h589
                                        · rcases p565_3 (m.d 0 3) (by simp) with h590 | h590
                                          · rcases p565_3 (m.d 0 4) (by simp) with h591 | h591
                                            · rcases p565_3 (m.d 0 5) (by simp) with h592 | h592
                                              · linarith only [h553, h592, hlam]
                                              · rcases h3bigk with h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h529, h555, h563, h564, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p594_1]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h529, h563, h564, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p594_1]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h529, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  rcases p594_3 (m.d 0 3) (by simp) with h599 | h599
                                                  · rcases p594_3 (m.d 1 3) (by simp) with h600 | h600
                                                    · linarith only [h524, h600, hlam]
                                                    · linarith only [h559, h600, hlam]
                                                  · linarith only [h599, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h524, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h524, h563, h564, hc45, hlam, hphi, ht0b, ht5b, p594_1, u0elo0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h557, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h0, h525, h557, h564, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p594_1]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h527, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h555, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h561, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h527, h564, hc45, hlam, hphi, ht0b, ht5b, p594_1, u0elo1]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h526, h556, h563, h564, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p565_1, p594_1]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  rcases p594_3 (m.d 0 3) (by simp) with h615 | h615
                                                  · linarith only [h529, h615, hlam]
                                                  · linarith only [h524, h615, hlam]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  rcases p594_3 (m.d 0 3) (by simp) with h618 | h618
                                                  · linarith only [h529, h618, hlam]
                                                  · linarith only [h527, h618, hlam]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h526, h529, h556, h563, hlam, p565_1, p594_2]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h553, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h559, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h563, hlam, p594_0]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [h564, hlam, p594_1]
                                                · have p594_0 := h594c.1
                                                  have p594_1 := h594c.2.1
                                                  have p594_2 := h594c.2.2.1
                                                  have p594_3 := h594c.2.2.2
                                                  linarith only [hlam, p594_0]
                                            · linarith only [h554, h591, hlam]
                                          · linarith only [h553, h590, hlam]
                                        · linarith only [h528, h589, hlam]
                                      · linarith only [h526, h588, hlam]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h525, hlam, p565_1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h0, h525, hc14, hlam, hphi, ht0b, ht45, ht5b, p565_1, u0elo3]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h524, h525, h555, h563, h564, hc45, hlam, hphi, ht0b, ht5b, p565_1, u0elo0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      rcases p565_3 (m.d 0 1) (by simp) with h636 | h636
                                      · rcases p565_3 (m.d 0 2) (by simp) with h637 | h637
                                        · rcases p565_3 (m.d 0 3) (by simp) with h638 | h638
                                          · linarith only [h529, h638, hlam]
                                          · linarith only [h553, h638, hlam]
                                        · linarith only [h528, h637, hlam]
                                      · linarith only [h526, h636, hlam]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h526, hlam, p565_1]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h528, hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h553, hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [h554, hlam, p565_0]
                                    · have p565_0 := h565c.1
                                      have p565_1 := h565c.2.1
                                      have p565_2 := h565c.2.2.1
                                      have p565_3 := h565c.2.2.2
                                      linarith only [hlam, p565_0]
                                  · linarith only [h564, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h563, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h557, h560, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h555, h559, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h556, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h527, h555, hlam]
                  · linarith only [h529, h554, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h527, h553, hc23, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h528, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h524, h527, hlam]
        · linarith only [h526, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h659 | h659
        · rcases m.htr 0 2 3 (by decide) (by decide) with h660 | h660
          · rcases m.htr 0 2 5 (by decide) (by decide) with h661 | h661
            · rcases m.htr 0 3 4 (by decide) (by decide) with h662 | h662
              · linarith only [h524, h525, h662, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
                · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h668 | h668
                        · linarith only [h524, h662, h668, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                              · linarith only [h524, h525, h666, h668, h672, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                                  · rcases h0bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h0, hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h525, h668, hc03, hc34, hlam, hphi, p676_1]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h525, hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      rcases p676_3 (m.d 0 1) (by simp) with h681 | h681
                                      · rcases p676_3 (m.d 0 2) (by simp) with h682 | h682
                                        · rcases p676_3 (m.d 0 3) (by simp) with h683 | h683
                                          · linarith only [h524, h683, hlam]
                                          · linarith only [h664, h683, hlam]
                                        · linarith only [h661, h682, hlam]
                                      · linarith only [h659, h681, hlam]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h524, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1, u0elo1]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h664, h675, hc45, hlam, hphi, ht0b, ht5b, p676_1, u0elo1]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h524, h525, h666, h674, h675, hc45, hlam, hphi, ht0b, ht5b, p676_1, u0elo1]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      rcases p676_3 (m.d 0 1) (by simp) with h692 | h692
                                      · linarith only [h0, h692, hlam]
                                      · linarith only [h659, h692, hlam]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h524, hlam, p676_1]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h660, hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h662, hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      rcases p676_3 (m.d 0 1) (by simp) with h699 | h699
                                      · rcases p676_3 (m.d 0 2) (by simp) with h700 | h700
                                        · rcases p676_3 (m.d 0 3) (by simp) with h701 | h701
                                          · rcases p676_3 (m.d 0 4) (by simp) with h702 | h702
                                            · rcases p676_3 (m.d 0 5) (by simp) with h703 | h703
                                              · linarith only [h664, h703, hlam]
                                              · rcases h3bigk with h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h524, h525, h666, h668, h674, h675, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p705_1]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h524, h525, h668, h674, h675, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p705_1]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h662, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  rcases p705_3 (m.d 0 3) (by simp) with h710 | h710
                                                  · rcases p705_3 (m.d 1 3) (by simp) with h711 | h711
                                                    · linarith only [h524, h711, hlam]
                                                    · linarith only [h670, h711, hlam]
                                                  · linarith only [h710, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h524, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h524, h525, h668, h674, h675, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p705_1]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h668, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h524, h525, h668, h675, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p705_1]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h660, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h666, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h672, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h660, h675, hc45, hlam, hphi, ht0b, ht5b, p705_1, u0elo1]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h659, h667, h674, h675, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p676_1, p705_1]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  rcases p705_3 (m.d 0 3) (by simp) with h726 | h726
                                                  · linarith only [h662, h726, hlam]
                                                  · linarith only [h524, h726, hlam]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  rcases p705_3 (m.d 0 3) (by simp) with h729 | h729
                                                  · linarith only [h662, h729, hlam]
                                                  · linarith only [h660, h729, hlam]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h524, h525, h659, h667, h668, h674, hlam, p676_1, p705_2]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h664, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h670, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h674, hlam, p705_0]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [h675, hlam, p705_1]
                                                · have p705_0 := h705c.1
                                                  have p705_1 := h705c.2.1
                                                  have p705_2 := h705c.2.2.1
                                                  have p705_3 := h705c.2.2.2
                                                  linarith only [hlam, p705_0]
                                            · linarith only [h665, h702, hlam]
                                          · linarith only [h664, h701, hlam]
                                        · linarith only [h661, h700, hlam]
                                      · linarith only [h659, h699, hlam]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h524, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1, u0elo3]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h0, h524, h666, h674, h675, hc45, hlam, hphi, ht0b, ht5b, p676_1, u0elo3]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h524, h666, h674, h675, hc45, hlam, hphi, ht0b, ht5b, p676_1, u0elo3]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      rcases p676_3 (m.d 0 1) (by simp) with h747 | h747
                                      · linarith only [h525, h747, hlam]
                                      · linarith only [h659, h747, hlam]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h659, hlam, p676_1]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h661, hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h664, hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [h665, hlam, p676_0]
                                    · have p676_0 := h676c.1
                                      have p676_1 := h676c.2.1
                                      have p676_2 := h676c.2.2.1
                                      have p676_3 := h676c.2.2.2
                                      linarith only [hlam, p676_0]
                                  · linarith only [h524, h525, h666, h668, h674, h675, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h674, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h524, h525, h671, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h666, h670, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h524, h666, h667, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h0, h660, h666, hlam]
                  · linarith only [h665, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h664, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h661, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h524, h660, hlam]
        · linarith only [h659, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h766 | h766
      · rcases m.htr 0 1 5 (by decide) (by decide) with h767 | h767
        · rcases m.htr 0 2 3 (by decide) (by decide) with h768 | h768
          · rcases m.htr 0 2 5 (by decide) (by decide) with h769 | h769
            · rcases m.htr 0 3 4 (by decide) (by decide) with h770 | h770
              · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
                · rcases m.htr 0 4 5 (by decide) (by decide) with h772 | h772
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h776 | h776
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h777 | h777
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h780 | h780
                                  · linarith only [h768, h778, h780, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h766, h777, h780, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h779, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h784 | h784
                                · linarith only [h770, h778, h784, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h784, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h777, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h524, h776, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h524, h770, h775, hlam]
                      · linarith only [h774, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h768, h773, hlam]
                  · linarith only [h772, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h771, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h524, h766, h770, hlam]
            · linarith only [h769, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h796 | h796
            · rcases m.htr 0 3 4 (by decide) (by decide) with h797 | h797
              · rcases m.htr 0 3 5 (by decide) (by decide) with h798 | h798
                · rcases m.htr 0 4 5 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h801 | h801
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h802 | h802
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h803 | h803
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h804 | h804
                            · linarith only [h0, h766, h768, h800, h804, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h802, h804, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h768, h800, h803, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h768, h797, h800, h802, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h768, h800, h801, hc03, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h810 | h810
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h811 | h811
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h812 | h812
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h813 | h813
                            · linarith only [h0, h766, h800, h813, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h813, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h800, h812, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h797, h800, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h766, h810, hc14, hlam, hphi, ht45, u5elo2]
                  · linarith only [h799, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h798, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h766, h768, h797, hlam]
            · linarith only [h0, h766, h796, hc14, hlam, hphi, ht45, u5elo2]
        · linarith only [h766, h767, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h824 | h824
        · rcases m.htr 0 2 3 (by decide) (by decide) with h825 | h825
          · rcases m.htr 0 2 5 (by decide) (by decide) with h826 | h826
            · rcases m.htr 0 3 4 (by decide) (by decide) with h827 | h827
              · rcases m.htr 0 3 5 (by decide) (by decide) with h828 | h828
                · rcases m.htr 0 4 5 (by decide) (by decide) with h829 | h829
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h831 | h831
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h832 | h832
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h835 | h835
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h836 | h836
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h837 | h837
                                  · linarith only [h825, h835, h837, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h837, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h836, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h841 | h841
                                · linarith only [h827, h835, h841, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h841, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h766, h834, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h524, h833, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h524, h827, h832, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h524, h824, h830, h831, hc15, hlam, hphi, u5elo2]
                    · linarith only [h0, h825, h830, hlam]
                  · linarith only [h766, h824, h829, hc15, hlam, hphi, u5elo4]
                · linarith only [h828, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h851 | h851
                · rcases m.htr 0 4 5 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h854 | h854
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h856 | h856
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h857 | h857
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h858 | h858
                              · linarith only [h524, h824, h825, h827, h854, h858, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h860 | h860
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h861 | h861
                                  · rcases h0bigk with h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h0, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h524, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h766, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h524, h824, h827, h853, h854, h855, h860, h861, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p862_1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h824, h854, h860, h861, hc45, hlam, hphi, ht0b, ht5b, p862_1, u0elo1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h524, h824, h854, h860, h861, hc45, hlam, hphi, ht0b, ht5b, p862_1, u0elo1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h524, h824, h827, h854, h860, h861, hc45, hlam, hphi, ht0b, ht5b, p862_1, u0elo1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      rcases p862_3 (m.d 0 1) (by simp) with h872 | h872
                                      · linarith only [h0, h872, hlam]
                                      · linarith only [h824, h872, hlam]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h824, h854, h860, h861, hc45, hlam, hphi, ht0b, ht5b, p862_1, u0elo2]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h825, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h827, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h824, h827, h853, h854, h855, h860, h861, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p862_1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h824, h827, h853, h854, h855, h860, h861, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p862_1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h0, h824, h827, h853, h854, h855, h860, h861, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p862_1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h524, h824, h827, h853, h854, h855, h860, h861, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p862_1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      rcases p862_3 (m.d 0 1) (by simp) with h884 | h884
                                      · linarith only [h766, h884, hlam]
                                      · linarith only [h824, h884, hlam]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h824, hlam, p862_1]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h826, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h851, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [h852, hlam, p862_0]
                                    · have p862_0 := h862c.1
                                      have p862_1 := h862c.2.1
                                      have p862_2 := h862c.2.2.1
                                      have p862_3 := h862c.2.2.2
                                      linarith only [hlam, p862_0]
                                  · linarith only [h827, h861, hc04, hlam, hphi, ht45, u5elo4]
                                · linarith only [h860, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h524, h827, h855, h857, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h524, h824, h827, h854, h855, h856, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h896 | h896
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h897 | h897
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h898 | h898
                              · linarith only [h524, h824, h854, h855, h898, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h900 | h900
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h901 | h901
                                  · rcases h0bigk with h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h0, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h524, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h766, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h524, h824, h854, h855, h900, h901, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p902_1]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h824, h854, h900, h901, hc45, hlam, hphi, ht0b, ht5b, p902_1, u0elo1]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h524, h824, h854, h900, h901, hc45, hlam, hphi, ht0b, ht5b, p902_1, u0elo1]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h524, h824, h827, h854, h900, h901, hc45, hlam, hphi, ht0b, ht5b, p902_1, u0elo1]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      rcases p902_3 (m.d 0 1) (by simp) with h912 | h912
                                      · linarith only [h0, h912, hlam]
                                      · linarith only [h824, h912, hlam]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h824, h854, h900, h901, hc45, hlam, hphi, ht0b, ht5b, p902_1, u0elo2]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h825, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h827, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      rcases p902_3 (m.d 0 1) (by simp) with h919 | h919
                                      · linarith only [h524, h919, hlam]
                                      · linarith only [h824, h919, hlam]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h824, h854, h900, h901, hc45, hlam, hphi, ht0b, ht5b, p902_1, u0elo3]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h825, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p902_1, u0elo3]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h524, h824, h854, h900, h901, hc45, hlam, hphi, ht0b, ht5b, p902_1, u0elo3]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      rcases p902_3 (m.d 0 1) (by simp) with h926 | h926
                                      · linarith only [h766, h926, hlam]
                                      · linarith only [h824, h926, hlam]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h824, hlam, p902_1]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h826, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h851, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [h852, hlam, p902_0]
                                    · have p902_0 := h902c.1
                                      have p902_1 := h902c.2.1
                                      have p902_2 := h902c.2.2.1
                                      have p902_3 := h902c.2.2.2
                                      linarith only [hlam, p902_0]
                                  · linarith only [h524, h824, h854, h855, h900, h901, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h900, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h766, h897, hc04, hlam, hphi, ht45, u5elo4]
                          · linarith only [h524, h896, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h524, h853, h854, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h824, h825, h853, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h827, h852, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h524, h824, h851, hc15, hlam, hphi, u5elo3]
            · linarith only [h826, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h943 | h943
            · rcases m.htr 0 3 4 (by decide) (by decide) with h944 | h944
              · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
                · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h948 | h948
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h949 | h949
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h953 | h953
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h954 | h954
                                  · rcases h0bigk with h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h524, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h766, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, h825, h947, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h825, h947, hc01, hc12, hlam, hphi, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h825, hlam, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h825, h947, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h824, h825, h947, h948, h953, h954, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h824, h948, h953, h954, hc45, hlam, hphi, ht0b, ht5b, p955_1, u0elo2]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, h824, h825, h947, h948, h953, h954, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h766, h824, h825, h947, h948, h953, h954, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      rcases p955_3 (m.d 0 1) (by simp) with h970 | h970
                                      · linarith only [h524, h970, hlam]
                                      · linarith only [h824, h970, hlam]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h824, h948, h953, h954, hc45, hlam, hphi, ht0b, ht5b, p955_1, u0elo3]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, h824, h825, h944, h947, h948, h953, h954, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h944, hlam, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      rcases p955_3 (m.d 0 1) (by simp) with h977 | h977
                                      · linarith only [h766, h977, hlam]
                                      · linarith only [h824, h977, hlam]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h824, hlam, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h943, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h945, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h946, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                  · linarith only [h954, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h825, h953, hc03, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h0, h825, h944, h952, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h766, h951, hc04, hlam, hphi, ht45, u5elo4]
                          · linarith only [h825, h947, h950, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h824, h825, h944, h947, h948, h949, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h825, h944, h947, h948, hc34, hlam, hphi, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h992 | h992
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h994 | h994
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h995 | h995
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h996 | h996
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h997 | h997
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h998 | h998
                                  · rcases h0bigk with h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h0, hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h524, hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h766, hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h0, h947, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p999_1]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h0, h947, hc01, hc23, hlam, hphi, ht12, p999_1]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h825, hlam, p999_1]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h0, h766, h824, h947, h992, h997, h998, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p999_1]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      rcases p999_3 (m.d 0 1) (by simp) with h1009 | h1009
                                      · linarith only [h0, h1009, hlam]
                                      · linarith only [h1009, h824, hlam]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h824, h992, h997, h998, hc45, hlam, hphi, ht0b, ht5b, p999_1, u0elo2]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h0, h824, h992, h997, h998, hc45, hlam, hphi, ht0b, ht5b, p999_1, u0elo2]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h766, h824, h992, h997, h998, hc45, hlam, hphi, ht0b, ht5b, p999_1, u0elo2]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      rcases p999_3 (m.d 0 1) (by simp) with h1016 | h1016
                                      · linarith only [h1016, h524, hlam]
                                      · linarith only [h1016, h824, hlam]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h824, h992, h997, h998, hc45, hlam, hphi, ht0b, ht5b, p999_1, u0elo3]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h0, h824, h944, h992, h997, h998, hc45, hlam, hphi, ht0b, ht5b, p999_1, u0elo2]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h944, hlam, p999_1]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      rcases p999_3 (m.d 0 1) (by simp) with h1023 | h1023
                                      · linarith only [h1023, h766, hlam]
                                      · linarith only [h1023, h824, hlam]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h824, hlam, p999_1]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h943, hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h945, hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [h946, hlam, p999_0]
                                    · have p999_0 := h999c.1
                                      have p999_1 := h999c.2.1
                                      have p999_2 := h999c.2.2.1
                                      have p999_3 := h999c.2.2.2
                                      linarith only [hlam, p999_0]
                                  · linarith only [h998, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h947, h997, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h824, h947, h992, h996, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h766, h995, hc04, hlam, hphi, ht45, u5elo4]
                          · linarith only [h524, h994, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h824, h944, h947, h992, h993, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h0, h824, h992, hc15, hlam, hphi, u5elo2]
                  · linarith only [h946, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h945, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1040 | h1040
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1041 | h1041
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1042 | h1042
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1043 | h1043
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1044 | h1044
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1045 | h1045
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1046 | h1046
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1047 | h1047
                              · linarith only [h0, h1042, h1043, h1047, h824, h825, h944, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h1042, h1043, h1044, h1047, h824, h825, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1046, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1045, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1052 | h1052
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1053 | h1053
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1054 | h1054
                              · linarith only [h1042, h1044, h1054, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1056 | h1056
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1057 | h1057
                                  · rcases h0bigk with h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c | h1058c
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h0, hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h524, hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h766, hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h0, h1042, h1044, h825, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1058_1]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1042, h1044, h825, hc01, hc34, hlam, hphi, ht12, ht23, p1058_1]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h825, hlam, p1058_1]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h825, h944, hlam, p1058_1]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1042, h1043, h1044, h1056, h1057, h824, h825, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1058_1]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1043, h1056, h1057, h824, hc45, hlam, hphi, ht0b, ht5b, p1058_1, u0elo2]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1042, h1044, h825, hc02, hc34, hlam, hphi, ht23, p1058_1]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h944, hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      rcases p1058_3 (m.d 0 1) (by simp) with h1073 | h1073
                                      · linarith only [h1073, h524, hlam]
                                      · linarith only [h1073, h824, hlam]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1043, h1056, h1057, h824, hc45, hlam, hphi, ht0b, ht5b, p1058_1, u0elo3]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h0, h1043, h1056, h1057, h824, hc45, hlam, hphi, ht0b, ht5b, p1058_1, u0elo3]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1043, h1056, h1057, h524, h824, hc45, hlam, hphi, ht0b, ht5b, p1058_1, u0elo3]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      rcases p1058_3 (m.d 0 1) (by simp) with h1080 | h1080
                                      · linarith only [h1080, h766, hlam]
                                      · linarith only [h1080, h824, hlam]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h824, hlam, p1058_1]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h943, hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1040, hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [h1041, hlam, p1058_0]
                                    · have p1058_0 := h1058c.1
                                      have p1058_1 := h1058c.2.1
                                      have p1058_2 := h1058c.2.2.1
                                      have p1058_3 := h1058c.2.2.2
                                      linarith only [hlam, p1058_0]
                                  · linarith only [h1042, h1044, h1057, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h0, h1043, h1056, h824, h825, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1053, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1042, h1043, h1052, h824, h825, hc25, hlam, hphi, u5elo3]
                      · linarith only [h1043, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1093 | h1093
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1094 | h1094
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1095 | h1095
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1096 | h1096
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1097 | h1097
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1098 | h1098
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1099 | h1099
                                  · rcases h0bigk with h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h0, hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h524, hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h766, hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h0, h1042, h1094, h825, h944, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1042, h1094, h825, h944, hc01, hc23, hlam, hphi, ht12, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h825, hlam, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1042, h1094, h825, h944, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1042, h1093, h1094, h1098, h1099, h824, h825, h944, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1042, h1093, h1094, h1098, h1099, h824, h944, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1042, h1094, h944, hc02, hc23, hlam, hphi, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h944, hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1042, h1093, h1094, h1098, h1099, h824, h944, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1093, h1098, h1099, h824, hc45, hlam, hphi, ht0b, ht5b, p1100_1, u0elo3]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h0, h1042, h1093, h1094, h1098, h1099, h824, h944, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1042, h1093, h1094, h1098, h1099, h524, h824, h944, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      rcases p1100_3 (m.d 0 1) (by simp) with h1120 | h1120
                                      · linarith only [h1120, h766, hlam]
                                      · linarith only [h1120, h824, hlam]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h824, hlam, p1100_1]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h943, hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1040, hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [h1041, hlam, p1100_0]
                                    · have p1100_0 := h1100c.1
                                      have p1100_1 := h1100c.2.1
                                      have p1100_2 := h1100c.2.2.1
                                      have p1100_3 := h1100c.2.2.2
                                      linarith only [hlam, p1100_0]
                                  · linarith only [h1099, h944, hc04, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h1042, h1094, h1098, h825, h944, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h1042, h1094, h1097, hlam]
                            · linarith only [h0, h1094, h1096, h825, h944, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h1093, h1094, h1095, h824, h825, h944, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1133 | h1133
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1134 | h1134
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1135 | h1135
                              · linarith only [h1093, h1094, h1135, h524, h824, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h1042, h1093, h1135, h824, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h1042, h1093, h1094, h1134, h824, hc25, hlam, hphi, u5elo4]
                          · linarith only [h0, h1042, h1093, h1133, h824, hc25, hlam, hphi, u5elo3]
                      · linarith only [h0, h1093, h824, hc15, hlam, hphi, u5elo2]
                  · linarith only [h0, h1041, h824, h825, h944, hc15, hlam, hphi, u5elo4]
                · linarith only [h0, h1040, h824, h825, hc15, hlam, hphi, u5elo3]
            · linarith only [h0, h824, h943, hc15, hlam, hphi, u5elo2]
        · linarith only [h824, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT3_M_LI_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h3elo := hb3.1
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
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h11, h6, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h5, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, h4, h9, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
                        · linarith only [h0, h17, h4, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h1, h20, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h20, h7, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                            · linarith only [h19, h23, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h23, h7, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h28, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h26, h28, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h26, h27, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                      · linarith only [h0, h26, h32, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h0, h26, h34, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                            · linarith only [h1, h37, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h37, h7, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h36, h40, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h40, h7, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                        · linarith only [h0, h46, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h44, h46, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h44, h45, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h44, h7, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                        · linarith only [h0, h53, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h0, h51, h53, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h5, h51, h52, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h51, h7, hc12, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
                · linarith only [h4, h58, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h60 | h60
                  · linarith only [h5, h6, h60, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                        · linarith only [h0, h64, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h67 | h67
                            · linarith only [h58, h67, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                              · linarith only [h2, h60, h69, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                                · linarith only [h3, h62, h64, h71, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h66, h71, hc23, hlam, hphi, u3elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                            · linarith only [h58, h6, h66, h74, hc02, hlam, hphi, ht23, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                              · linarith only [h2, h60, h76, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                                · linarith only [h0, h62, h78, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                                  · linarith only [h3, h58, h63, h64, h78, h80, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h4, h6, h80, hc23, hlam, hphi, u3elo4]
                      · linarith only [h5, h62, h63, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h4, h58, h6, h62, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h85 | h85
              · rcases m.htr 0 3 5 (by decide) (by decide) with h86 | h86
                · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                      · linarith only [h0, h5, h89, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
                        · linarith only [h2, h89, h91, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h5, h85, h88, h91, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h4, h5, h88, hc12, hc24, hlam, hphi]
                  · linarith only [h4, h5, h86, h87, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h96 | h96
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                      · linarith only [h0, h5, h98, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                        · linarith only [h0, h100, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h100, h5, h85, hc12, hc24, hlam, hphi]
                    · linarith only [h4, h5, h97, hc12, hc24, hlam, hphi]
                  · linarith only [h5, h85, h96, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h105 | h105
                · linarith only [h105, h4, h85, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                      · linarith only [h0, h109, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                        · linarith only [h0, h111, h85, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                          · linarith only [h1, h105, h108, h109, h113, hc23, hlam, hphi, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                            · linarith only [h105, h115, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                              · linarith only [h117, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h107, h108, h109, h117, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h108, h4, h85, hc12, hc25, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                      · linarith only [h0, h122, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                        · linarith only [h0, h124, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                          · linarith only [h1, h105, h121, h122, h126, hc23, hlam, hphi, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                            · linarith only [h1, h105, h128, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                              · linarith only [h130, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                                · linarith only [h126, h132, hc13, hlam, hphi, u3elo2]
                                · linarith only [h132, h4, h5, hc23, hlam, hphi, u3elo3]
                    · linarith only [h121, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h136 | h136
            · rcases m.htr 0 2 5 (by decide) (by decide) with h137 | h137
              · linarith only [h137, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h139 | h139
                · rcases m.htr 0 4 5 (by decide) (by decide) with h140 | h140
                  · linarith only [h136, h140, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
                    · linarith only [h0, h142, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                        · linarith only [h0, h137, h145, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                            · linarith only [h1, h148, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h139, h148, hc13, hlam, hphi, u3elo0]
                          · linarith only [h142, h144, h147, hlam]
                      · linarith only [h136, h144, h4, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h136, h139, h153, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                    · linarith only [h0, h139, h155, h4, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h137, h155, h158, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                            · linarith only [h1, h139, h161, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                              · linarith only [h153, h163, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                                  · linarith only [h139, h166, h4, hc02, hlam, hphi, ht23, u3elo2]
                                  · linarith only [h0, h157, h165, h166, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h0, h157, h165, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h155, h157, h160, hlam]
                      · linarith only [h136, h157, h4, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h172 | h172
              · linarith only [h172, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h174 | h174
                · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                    · linarith only [h0, h176, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
                      · linarith only [h0, h136, h175, h178, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                        · linarith only [h0, h172, h180, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                            · linarith only [h1, h183, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h174, h182, h183, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                            · linarith only [h182, h186, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h174, h186, h4, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                    · linarith only [h0, h189, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
                      · linarith only [h136, h189, h191, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h193 | h193
                        · linarith only [h0, h172, h193, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                            · linarith only [h1, h196, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h174, h196, h4, hc13, hlam, hphi, u3elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                            · linarith only [h195, h199, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h174, h199, h4, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
                    · linarith only [h0, h174, h203, h4, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                      · linarith only [h136, h203, h205, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h207 | h207
                        · linarith only [h0, h172, h207, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h209 | h209
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                            · linarith only [h1, h174, h210, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                              · linarith only [h2, h212, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                                · linarith only [h136, h202, h205, h212, h214, hc12, hlam, hphi, ht23, u3elo2]
                                · linarith only [h1, h174, h209, h214, hc23, hlam, hphi, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
                            · linarith only [h174, h209, h217, hc03, hlam, hphi, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                              · linarith only [h2, h219, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                                · linarith only [h203, h209, h221, hc12, hlam, hphi, ht23, u3elo2]
                                · linarith only [h0, h221, h4, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                    · linarith only [h0, h224, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                      · linarith only [h0, h136, h226, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                        · linarith only [h0, h172, h228, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h231 | h231
                            · linarith only [h174, h231, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                              · linarith only [h2, h233, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                                  · linarith only [h174, h236, hc03, hlam, hphi, u3elo2]
                                  · linarith only [h0, h236, h4, hc12, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h1, h230, h235, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
                            · linarith only [h1, h174, h240, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                              · linarith only [h2, h202, h242, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                                · linarith only [h230, h244, hc13, hlam, hphi, u3elo2]
                                · linarith only [h0, h244, h4, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h247 | h247
          · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
            · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
              · linarith only [h0, h249, h3, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h251 | h251
                · linarith only [h1, h251, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
                  · linarith only [h0, h248, h253, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                    · linarith only [h0, h251, h255, h3, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h247, h251, h255, h3, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h258 | h258
              · linarith only [h2, h248, h258, h3, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h260 | h260
                · linarith only [h1, h260, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h2, h262, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h260, h264, h3, hc23, hlam, hphi, u3elo4]
                    · linarith only [h247, h248, h262, h264, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h267 | h267
            · rcases m.htr 0 2 5 (by decide) (by decide) with h268 | h268
              · linarith only [h247, h268, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h270 | h270
                · linarith only [h1, h270, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h272 | h272
                  · linarith only [h247, h267, h270, h272, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                    · linarith only [h0, h247, h270, h274, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                        · linarith only [h0, h247, h268, h277, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                            · linarith only [h1, h247, h270, h280, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h1, h274, h276, h280, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h274, h276, h279, hlam]
                      · linarith only [h247, h267, h270, h276, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h285 | h285
              · linarith only [h247, h285, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h287 | h287
                · linarith only [h1, h287, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
                  · linarith only [h2, h289, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                    · linarith only [h0, h247, h287, h291, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                      · linarith only [h1, h267, h287, h291, h293, h3, hc02, hlam, hphi, ht23, u3elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
                        · linarith only [h0, h247, h285, h295, h3, hc01, hlam, hphi, ht12, ht23, u3elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h297 | h297
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h298 | h298
                            · linarith only [h1, h287, h298, h3, hlam]
                            · linarith only [h1, h297, h298, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h301 | h301
                            · linarith only [h2, h297, h301, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h2, h297, h3, h301, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h304 | h304
        · rcases m.htr 0 2 3 (by decide) (by decide) with h305 | h305
          · rcases m.htr 0 2 4 (by decide) (by decide) with h306 | h306
            · linarith only [h0, h2, h306, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h308 | h308
              · rcases m.htr 0 3 5 (by decide) (by decide) with h309 | h309
                · rcases m.htr 0 4 5 (by decide) (by decide) with h310 | h310
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h312 | h312
                      · linarith only [h0, h305, h306, h309, h312, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h314 | h314
                        · linarith only [h0, h2, h312, h314, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h308, h311, h314, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h305, h306, h311, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h304, h310, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h319 | h319
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h321 | h321
                      · linarith only [h0, h306, h321, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h323 | h323
                        · linarith only [h0, h2, h321, h323, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h2, h308, h321, h323, hc12, hc24, hlam, hphi]
                    · linarith only [h305, h306, h320, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h304, h319, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h328 | h328
                · linarith only [h305, h308, h328, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
                      · linarith only [h0, h306, h332, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                        · linarith only [h0, h308, h334, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                          · linarith only [h1, h2, h328, h336, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h2, h304, h331, h334, h336, hc23, hlam, hphi, u3elo3]
                    · linarith only [h305, h308, h331, hc12, hc25, hlam, hphi]
                  · linarith only [h2, h304, h330, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h341 | h341
            · linarith only [h0, h2, h341, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h343 | h343
              · linarith only [h305, h343, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                    · linarith only [h0, h305, h347, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
                      · linarith only [h0, h2, h341, h349, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                        · linarith only [h1, h347, h351, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
                          · linarith only [h1, h2, h353, hlam]
                          · linarith only [h1, h2, h347, h353, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2, h304, h346, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
                    · linarith only [h0, h305, h345, h358, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h360 | h360
                      · linarith only [h0, h341, h360, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h362 | h362
                        · linarith only [h0, h343, h362, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
                          · linarith only [h1, h2, h364, hlam]
                          · linarith only [h1, h2, h364, hc13, hlam, hphi, u3elo3]
                  · linarith only [h2, h304, h357, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h368 | h368
          · rcases m.htr 0 2 4 (by decide) (by decide) with h369 | h369
            · linarith only [h0, h2, h369, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h371 | h371
              · linarith only [h0, h304, h371, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h373 | h373
                · linarith only [h0, h304, h368, h373, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                    · linarith only [h0, h304, h373, h376, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h304, h368, h373, h376, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
                    · linarith only [h0, h2, h373, h375, h379, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h2, h368, h373, h375, h379, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h382 | h382
            · linarith only [h0, h2, h382, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h384 | h384
              · linarith only [h368, h384, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h386 | h386
                · linarith only [h1, h304, h386, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                    · linarith only [h0, h368, h386, h389, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                      · linarith only [h1, h304, h382, h388, h389, h391, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
                        · linarith only [h1, h304, h384, h389, h393, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h395 | h395
                          · linarith only [h1, h2, h395, hlam]
                          · linarith only [h1, h2, h389, h395, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                    · linarith only [h0, h368, h398, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h400 | h400
                      · linarith only [h1, h2, h388, h398, h400, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                        · linarith only [h1, h398, h402, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h404 | h404
                          · linarith only [h1, h2, h388, h404, hc34, hc45, hlam, hphi]
                          · linarith only [h1, h2, h398, h404, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h408 | h408
    · rcases m.htr 0 1 4 (by decide) (by decide) with h409 | h409
      · rcases m.htr 0 1 5 (by decide) (by decide) with h410 | h410
        · rcases m.htr 0 2 3 (by decide) (by decide) with h411 | h411
          · rcases m.htr 0 2 4 (by decide) (by decide) with h412 | h412
            · rcases m.htr 0 2 5 (by decide) (by decide) with h413 | h413
              · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
                · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h417 | h417
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h418 | h418
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h420 | h420
                            · linarith only [h408, h420, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h414, h419, h420, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h423 | h423
                            · linarith only [h419, h423, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h414, h423, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h410, h418, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h408, h414, h417, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h408, h414, h416, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h429 | h429
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h433 | h433
                            · linarith only [h408, h433, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h414, h433, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h436 | h436
                            · linarith only [h432, h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h414, h436, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h410, h431, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h408, h414, h430, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h408, h414, h429, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h444 | h444
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h445 | h445
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h447 | h447
                            · linarith only [h408, h414, h447, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                              · linarith only [h408, h414, h446, h449, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h451 | h451
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                                  · linarith only [h408, h414, h443, h452, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h454 | h454
                                    · linarith only [h444, h449, h454, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h456 | h456
                                      · linarith only [h408, h414, h443, h449, h451, h456, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                      · linarith only [h414, h442, h456, hlam]
                                · linarith only [h408, h414, h446, h451, hc23, hlam, hphi, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                            · linarith only [h414, h446, h460, hc03, hlam, hphi, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h462 | h462
                              · linarith only [h0, h409, h462, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                                · linarith only [h0, h409, h442, h443, h446, h462, h464, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
                                  · linarith only [h414, h443, h446, h466, hc03, hlam, hphi, u3elo3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h468 | h468
                                    · linarith only [h444, h462, h468, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h470 | h470
                                      · linarith only [h443, h446, h462, h470, hc23, hlam, hphi, u3elo3]
                                      · linarith only [h0, h409, h442, h443, h446, h470, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h409, h442, h445, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h409, h442, h444, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h409, h442, h443, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h478 | h478
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h479 | h479
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
                            · linarith only [h408, h414, h480, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                              · linarith only [h408, h414, h442, h479, h482, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                                  · linarith only [h408, h414, h476, h485, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                                    · linarith only [h409, h442, h477, h487, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                                      · linarith only [h408, h414, h442, h476, h484, h489, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                      · rcases h5bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, p491_0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, hphi, ht0b, ht5b, p491_1, u0elo4, u5ehi1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h410, hlam, hphi, ht0b, ht5b, p491_1, u0elo0, u5ehi2]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h414, hlam, p491_0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h442, hlam, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h410, hlam, p491_0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, p491_0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h0, h410, hc12, hlam, hphi, ht01, ht0b, ht5b, p491_1, u5ehi2]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h480, hlam, p491_0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h482, hlam, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h413, hlam, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h478, hlam, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, p491_0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h485, hlam, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h487, hlam, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p491_1, u3elo4, u5ehi0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h478, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p491_1, u3elo4, u5ehi2]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p491_1, u3elo4, u5ehi2]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, p491_0]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h489, hlam, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h408, h414, h476, h484, hc34, hc45, hlam, hphi, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h476, h480, h484, hc34, hc45, hlam, hphi, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h484, h485, hc34, hc45, hlam, hphi, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [h408, h414, h476, h484, hc34, hc45, hlam, hphi, p491_1]
                                        · have p491_0 := h491c.1
                                          have p491_1 := h491c.2.1
                                          have p491_2 := h491c.2.2.1
                                          have p491_3 := h491c.2.2.2
                                          linarith only [hlam, p491_0]
                                · linarith only [h408, h414, h479, h484, hc23, hlam, hphi, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h518 | h518
                            · linarith only [h414, h479, h518, hc03, hlam, hphi, u3elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h520 | h520
                              · linarith only [h0, h409, h520, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                                · linarith only [h476, h479, h522, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                                  · linarith only [h408, h414, h476, h524, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h526 | h526
                                    · linarith only [h412, h442, h526, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h528 | h528
                                      · linarith only [h409, h442, h476, h479, h528, hc23, hlam, hphi, u3elo3]
                                      · rcases h5bigk with h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [hlam, p530_0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h478, hlam, hphi, ht0b, ht5b, p530_1, u0elo4, u5ehi2]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h0, h410, hc12, hlam, hphi, ht01, ht0b, ht5b, p530_1, u5ehi2]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h414, hlam, p530_0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h442, hlam, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h410, hlam, p530_0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [hlam, p530_0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h0, h410, hc12, hlam, hphi, ht01, ht0b, ht5b, p530_1, u5ehi2]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h518, hlam, p530_0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h520, hlam, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h413, hlam, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h478, hlam, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [hlam, p530_0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h524, hlam, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h526, hlam, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p530_1, u3elo4, u5ehi0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h478, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p530_1, u3elo4, u5ehi2]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p530_1, u3elo4, u5ehi2]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [hlam, p530_0]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h528, hlam, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          rcases p530_3 (m.d 0 5) (by simp) with h551 | h551
                                          · linarith only [h442, h551, hlam]
                                          · rcases p530_3 (m.d 1 5) (by simp) with h553 | h553
                                            · linarith only [h520, h553, hlam]
                                            · rcases p530_3 (m.d 2 5) (by simp) with h555 | h555
                                              · linarith only [h526, h555, hlam]
                                              · rcases p530_3 (m.d 3 5) (by simp) with h557 | h557
                                                · linarith only [h528, h557, hlam]
                                                · linarith only [h414, h557, hlam]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          rcases p530_3 (m.d 0 5) (by simp) with h560 | h560
                                          · linarith only [h442, h560, hlam]
                                          · linarith only [h410, h560, hlam]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          rcases p530_3 (m.d 0 5) (by simp) with h563 | h563
                                          · linarith only [h442, h563, hlam]
                                          · linarith only [h413, h563, hlam]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [h408, h414, h476, hc23, hc45, hlam, hphi, ht34, p530_1]
                                        · have p530_0 := h530c.1
                                          have p530_1 := h530c.2.1
                                          have p530_2 := h530c.2.2.1
                                          have p530_3 := h530c.2.2.2
                                          linarith only [hlam, p530_0]
                        · linarith only [h0, h410, h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h410, h477, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h410, h476, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h410, h413, hlam]
            · linarith only [h0, h409, h412, hlam]
          · linarith only [h0, h410, h411, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h574 | h574
          · rcases m.htr 0 2 4 (by decide) (by decide) with h575 | h575
            · rcases m.htr 0 2 5 (by decide) (by decide) with h576 | h576
              · rcases m.htr 0 3 5 (by decide) (by decide) with h577 | h577
                · linarith only [h408, h410, h577, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h579 | h579
                  · linarith only [h409, h410, h579, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h581 | h581
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h582 | h582
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h583 | h583
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h584 | h584
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h585 | h585
                            · linarith only [h408, h410, h577, h585, hlam]
                            · linarith only [h408, h410, h584, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h588 | h588
                            · linarith only [h409, h577, h584, h588, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h408, h410, h581, h588, hc23, hlam, hphi, u3elo4]
                        · linarith only [h0, h576, h583, hlam]
                      · linarith only [h0, h575, h582, hlam]
                    · linarith only [h0, h581, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h594 | h594
                · linarith only [h408, h410, h594, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h596 | h596
                  · linarith only [h0, h409, h576, h596, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h599 | h599
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                          · linarith only [h0, h408, h576, h600, h601, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
                            · linarith only [h0, h409, h576, h594, h601, h603, hlam]
                            · linarith only [h0, h409, h576, h600, h601, h603, hc13, hlam, hphi, u3elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h606 | h606
                          · linarith only [h0, h408, h600, h606, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h608 | h608
                            · linarith only [h0, h409, h594, h600, h606, h608, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h409, h410, h598, h606, h608, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h575, h599, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h408, h598, hc13, hlam, hphi, u3elo2]
            · linarith only [h0, h409, h575, hlam]
          · linarith only [h0, h408, h574, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h615 | h615
        · rcases m.htr 0 2 3 (by decide) (by decide) with h616 | h616
          · rcases m.htr 0 2 4 (by decide) (by decide) with h617 | h617
            · rcases m.htr 0 2 5 (by decide) (by decide) with h618 | h618
              · rcases m.htr 0 3 5 (by decide) (by decide) with h619 | h619
                · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
                          · linarith only [h408, h409, h624, hlam]
                          · linarith only [h408, h409, h619, h624, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h408, h409, h619, h622, h623, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h408, h617, h619, h622, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                    · linarith only [h0, h408, h619, h621, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h408, h409, h619, h620, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h631 | h631
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h633 | h633
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h634 | h634
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h635 | h635
                          · linarith only [h408, h409, h635, hlam]
                          · linarith only [h408, h409, h635, hc13, hlam, hphi, u3elo3]
                        · linarith only [h409, h615, h633, h634, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h615, h617, h633, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
                    · linarith only [h0, h615, h632, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h409, h615, h631, hlam]
              · linarith only [h0, h615, h618, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h643 | h643
              · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
                · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h647 | h647
                      · linarith only [h0, h408, h617, h644, h647, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h408, h644, h647, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h408, h644, h646, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h408, h617, h644, h645, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h652 | h652
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
                      · linarith only [h617, h643, h654, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h615, h654, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h615, h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h615, h617, h652, hlam]
              · linarith only [h0, h615, h643, hlam]
          · linarith only [h0, h615, h616, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h661 | h661
          · rcases m.htr 0 2 4 (by decide) (by decide) with h662 | h662
            · rcases m.htr 0 2 5 (by decide) (by decide) with h663 | h663
              · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
                · linarith only [h408, h615, h664, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h666 | h666
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h670 | h670
                          · linarith only [h408, h409, h670, hlam]
                          · linarith only [h408, h409, h670, hc13, hlam, hphi, u3elo3]
                        · linarith only [h408, h409, h663, h667, h668, h669, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h662, h668, hlam]
                    · linarith only [h0, h408, h667, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h677 | h677
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h679 | h679
                          · linarith only [h408, h409, h666, h679, hc34, hc45, hlam, hphi]
                          · linarith only [h408, h409, h679, hc13, hlam, hphi, u3elo3]
                        · linarith only [h408, h409, h663, h676, h677, h678, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h408, h662, h676, h677, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h676, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h685 | h685
                · linarith only [h408, h615, h685, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
                  · linarith only [h662, h663, h687, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h690 | h690
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h691 | h691
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h692 | h692
                          · linarith only [h408, h409, h662, h663, h691, h692, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h408, h409, h689, h692, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h695 | h695
                          · linarith only [h408, h409, h690, h691, h695, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h408, h409, h689, h695, hc23, hlam, hphi, u3elo3]
                      · linarith only [h662, h663, h685, h690, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h689, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h700 | h700
              · rcases m.htr 0 3 5 (by decide) (by decide) with h701 | h701
                · linarith only [h408, h615, h701, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h703 | h703
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                      · linarith only [h662, h700, h705, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h707 | h707
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h708 | h708
                          · linarith only [h0, h408, h705, h708, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h408, h615, h705, h707, h708, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h408, h700, h704, h707, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h704, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h662, h700, h703, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h714 | h714
                · linarith only [h0, h408, h700, h714, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h716 | h716
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h718 | h718
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h720 | h720
                          · linarith only [h0, h408, h662, h718, h720, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h408, h409, h720, hc13, hlam, hphi, u3elo3]
                        · linarith only [h662, h718, h719, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                        · linarith only [h0, h408, h700, h717, h718, h724, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h726 | h726
                          · linarith only [h0, h408, h718, h726, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h408, h718, h726, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h408, h717, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h731 | h731
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
                          · linarith only [h0, h408, h662, h731, h733, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h408, h662, h730, h731, h733, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h408, h662, h730, h731, h732, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                        · linarith only [h0, h408, h700, h730, h731, h737, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h739 | h739
                          · linarith only [h0, h408, h662, h716, h739, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h408, h730, h731, h739, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h730, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h408, h661, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h744 | h744
      · rcases m.htr 0 1 5 (by decide) (by decide) with h745 | h745
        · linarith only [h408, h745, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h747 | h747
          · rcases m.htr 0 2 4 (by decide) (by decide) with h748 | h748
            · rcases m.htr 0 2 5 (by decide) (by decide) with h749 | h749
              · rcases m.htr 0 3 5 (by decide) (by decide) with h750 | h750
                · rcases m.htr 0 4 5 (by decide) (by decide) with h751 | h751
                  · linarith only [h408, h744, h751, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h754 | h754
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h755 | h755
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h756 | h756
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h757 | h757
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h758 | h758
                              · linarith only [h744, h745, h751, h757, h758, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h760 | h760
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h761 | h761
                                  · linarith only [h747, h761, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h750, h761, hc23, hlam, hphi, u3elo0]
                                · linarith only [h756, h760, hc23, hlam, hphi, u3elo1]
                            · linarith only [h408, h750, h757, hlam]
                          · linarith only [h408, h750, h756, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h0, h749, h755, hlam]
                      · linarith only [h0, h748, h754, hlam]
                    · linarith only [h0, h749, h753, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h770 | h770
                  · linarith only [h408, h744, h750, h770, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h776 | h776
                            · linarith only [h408, h744, h750, h773, h776, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h408, h744, h773, h776, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h408, h744, h773, h775, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h744, h749, h773, h774, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h748, h773, hlam]
                    · linarith only [h0, h747, h772, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h783 | h783
                · linarith only [h747, h749, h783, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h785 | h785
                  · linarith only [h408, h744, h785, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h787 | h787
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h788 | h788
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h789 | h789
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h790 | h790
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
                            · linarith only [h408, h783, h791, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h408, h744, h788, h791, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h408, h744, h788, h790, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h796 | h796
                            · linarith only [h408, h744, h783, h787, h788, h789, h796, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h408, h744, h788, h796, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h408, h744, h788, h795, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h748, h749, h783, h788, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h744, h747, h787, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
            · linarith only [h0, h744, h748, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h803 | h803
            · rcases m.htr 0 2 5 (by decide) (by decide) with h804 | h804
              · linarith only [h747, h804, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h806 | h806
                · rcases m.htr 0 4 5 (by decide) (by decide) with h807 | h807
                  · linarith only [h408, h744, h807, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h809 | h809
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h810 | h810
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h811 | h811
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h812 | h812
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h813 | h813
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h814 | h814
                              · linarith only [h744, h807, h814, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h816 | h816
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h817 | h817
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h818 | h818
                                    · linarith only [h0, h744, h804, h810, h811, h814, h818, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h820 | h820
                                      · linarith only [h0, h744, h804, h810, h811, h814, h816, h820, hlam]
                                      · rcases h5bigk with h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [hlam, p822_0]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h745, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h804, hlam, p822_0]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h747, h806, h809, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p822_1, u3elo1, u5ehi3]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h807, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h813, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p822_1, u3elo1, u5ehi0]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [hlam, p822_0]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h0, h804, h813, hc01, hlam, hphi, ht12, ht23, p822_1, u3elo1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h813, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p822_1, u3elo1, u5ehi3]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h814, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h0, h744, h804, h810, h811, h816, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h811, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [hlam, p822_0]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h811, h813, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p822_1, u3elo1, u5ehi3]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h818, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h806, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h813, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h817, hlam, p822_0]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [hlam, p822_0]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h820, hlam, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h0, h744, h804, h810, h816, hc34, hc45, hlam, hphi, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h744, h745, h810, h816, hc34, hc45, hlam, hphi, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [h0, h744, h804, h810, h816, hc34, hc45, hlam, hphi, p822_1]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          rcases p822_3 (m.d 0 5) (by simp) with h846 | h846
                                          · linarith only [h807, h846, hlam]
                                          · linarith only [h806, h846, hlam]
                                        · have p822_0 := h822c.1
                                          have p822_1 := h822c.2.1
                                          have p822_2 := h822c.2.2.1
                                          have p822_3 := h822c.2.2.2
                                          linarith only [hlam, p822_0]
                                  · linarith only [h0, h744, h747, h810, h816, h817, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h0, h744, h747, h810, h816, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h806, h813, hc13, hlam, hphi, u3elo0]
                          · linarith only [h0, h744, h747, h809, h810, h812, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h744, h747, h809, h810, h811, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h747, h809, h810, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h744, h809, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h857 | h857
                  · linarith only [h408, h744, h857, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h859 | h859
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h860 | h860
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h861 | h861
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h862 | h862
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h863 | h863
                            · linarith only [h0, h747, h806, h863, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h408, h744, h860, h863, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h0, h744, h747, h859, h860, h862, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h744, h747, h859, h860, h861, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h744, h747, h859, h860, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h744, h859, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h0, h744, h803, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h871 | h871
        · linarith only [h408, h871, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h873 | h873
          · rcases m.htr 0 2 4 (by decide) (by decide) with h874 | h874
            · rcases m.htr 0 2 5 (by decide) (by decide) with h875 | h875
              · rcases m.htr 0 3 5 (by decide) (by decide) with h876 | h876
                · rcases m.htr 0 4 5 (by decide) (by decide) with h877 | h877
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h879 | h879
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h880 | h880
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h883 | h883
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h884 | h884
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h885 | h885
                                  · linarith only [h873, h885, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h876, h884, h885, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h881, h884, hc23, hlam, hphi, u3elo1]
                              · linarith only [h744, h877, h883, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h744, h876, h877, h881, h882, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                          · linarith only [h408, h881, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h873, h875, h876, h880, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                      · linarith only [h0, h874, h879, hlam]
                    · linarith only [h0, h873, h876, h878, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h896 | h896
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h897 | h897
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h898 | h898
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h899 | h899
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h900 | h900
                              · linarith only [h744, h877, h898, h900, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h902 | h902
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h903 | h903
                                  · linarith only [h873, h903, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h876, h903, hc23, hlam, hphi, u3elo0]
                                · linarith only [h898, h902, hc23, hlam, hphi, u3elo1]
                            · linarith only [h408, h876, h899, hlam]
                          · linarith only [h408, h876, h898, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h0, h873, h875, h876, h897, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                      · linarith only [h0, h874, h875, h896, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                    · linarith only [h0, h873, h876, h895, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h912 | h912
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h913 | h913
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h915 | h915
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h916 | h916
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h917 | h917
                            · linarith only [h876, h917, hc03, hlam, hphi, u3elo1]
                            · linarith only [h408, h917, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h408, h916, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h875, h915, hlam]
                      · linarith only [h0, h874, h914, hlam]
                    · linarith only [h0, h873, h874, h912, h913, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h924 | h924
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h925 | h925
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h928 | h928
                            · linarith only [h876, h928, hc03, hlam, hphi, u3elo1]
                            · linarith only [h408, h928, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h408, h927, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h875, h926, hlam]
                      · linarith only [h0, h874, h925, hlam]
                    · linarith only [h0, h873, h924, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h935 | h935
                · linarith only [h873, h875, h935, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
                  · linarith only [h874, h875, h937, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
                            · linarith only [h935, h943, hc03, hlam, hphi, u3elo1]
                            · linarith only [h408, h943, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h408, h942, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h947 | h947
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h948 | h948
                            · linarith only [h408, h935, h948, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h408, h948, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h408, h947, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h874, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h939, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h954 | h954
              · rcases m.htr 0 3 5 (by decide) (by decide) with h955 | h955
                · rcases m.htr 0 4 5 (by decide) (by decide) with h956 | h956
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h957 | h957
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h958 | h958
                      · linarith only [h873, h874, h955, h958, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h960 | h960
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h961 | h961
                          · linarith only [h957, h958, h961, hlam]
                          · linarith only [h408, h961, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h954, h960, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h873, h957, hlam]
                  · linarith only [h873, h874, h955, h956, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h967 | h967
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h968 | h968
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h969 | h969
                      · linarith only [h874, h954, h969, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h971 | h971
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h972 | h972
                          · linarith only [h968, h969, h972, hlam]
                          · linarith only [h408, h972, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h954, h971, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h873, h954, h968, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
                  · linarith only [h874, h954, h967, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h978 | h978
                · linarith only [h873, h954, h978, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h980 | h980
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h981 | h981
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h982 | h982
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h983 | h983
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h984 | h984
                          · linarith only [h873, h874, h982, h984, hc23, hlam, hphi, u3elo1]
                          · linarith only [h408, h984, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h873, h874, h982, h983, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h988 | h988
                        · linarith only [h873, h954, h982, h988, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h990 | h990
                          · linarith only [h981, h982, h990, hlam]
                          · linarith only [h408, h990, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h873, h981, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h994 | h994
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h995 | h995
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h996 | h996
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h997 | h997
                          · linarith only [h873, h874, h995, h997, hc23, hlam, hphi, u3elo1]
                          · linarith only [h408, h997, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h873, h874, h995, h996, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1001 | h1001
                        · linarith only [h1001, h873, h954, h995, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1003 | h1003
                          · linarith only [h1003, h994, h995, hlam]
                          · linarith only [h1003, h408, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h873, h994, hc01, hlam, hphi, ht12, ht23, u3elo0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1007 | h1007
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1008 | h1008
              · linarith only [h1008, h873, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1011 | h1011
                  · linarith only [h1007, h1011, h873, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1013 | h1013
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1014 | h1014
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1015 | h1015
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1016 | h1016
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1017 | h1017
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1018 | h1018
                              · linarith only [h1011, h1016, h1018, h744, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1020 | h1020
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1021 | h1021
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1022 | h1022
                                    · linarith only [h1007, h1008, h1015, h1017, h1018, h1022, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1024 | h1024
                                      · linarith only [h1007, h1008, h1015, h1017, h1018, h1020, h1024, h744, hc01, hlam, hphi, ht12, ht23, u3elo1]
                                      · rcases h5bigk with h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c | h1026c
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [hlam, p1026_0]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h871, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1008, hlam, p1026_0]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [hlam, hphi, ht0b, ht5b, p1026_1, u0elo4, u5ehi3]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1011, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1017, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1026_1, u3elo1, u5ehi0]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [hlam, p1026_0]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1008, h1017, hc02, hlam, hphi, ht23, p1026_1, u3elo1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1017, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1026_1, u3elo1, u5ehi3]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1018, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1007, h1008, h1015, h1020, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1015, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [hlam, p1026_0]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1015, h1017, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1026_1, u3elo1, u5ehi3]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1022, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1010, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1017, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1021, hlam, p1026_0]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [hlam, p1026_0]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1024, hlam, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1007, h1008, h1020, hc34, hc45, hlam, hphi, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h871, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [h1007, h1008, h1020, hc34, hc45, hlam, hphi, p1026_1]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          rcases p1026_3 (m.d 0 5) (by simp) with h1050 | h1050
                                          · linarith only [h1011, h1050, hlam]
                                          · linarith only [h1010, h1050, hlam]
                                        · have p1026_0 := h1026c.1
                                          have p1026_1 := h1026c.2.1
                                          have p1026_2 := h1026c.2.2.1
                                          have p1026_3 := h1026c.2.2.2
                                          linarith only [hlam, p1026_0]
                                  · linarith only [h1007, h1020, h1021, h873, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h1007, h1020, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h1010, h1016, h1017, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h1016, h408, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1007, h1013, h1015, h873, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1007, h1013, h1014, h873, hlam]
                    · linarith only [h0, h1013, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1061 | h1061
                  · linarith only [h1007, h1061, h873, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1063 | h1063
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1064 | h1064
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1065 | h1065
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1066 | h1066
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1067 | h1067
                            · linarith only [h1010, h1067, h873, hc02, hlam, hphi, ht23, u3elo1]
                            · linarith only [h1067, h408, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1007, h1063, h1066, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h1007, h1063, h1065, h873, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1007, h1063, h1064, h873, hlam]
                    · linarith only [h0, h1063, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1074 | h1074
              · linarith only [h1074, h873, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1076 | h1076
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1077 | h1077
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1078 | h1078
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1079 | h1079
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1080 | h1080
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1081 | h1081
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1082 | h1082
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1083 | h1083
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1084 | h1084
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1086 | h1086
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1087 | h1087
                                      · linarith only [h1078, h1084, h1087, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                                      · rcases h5bigk with h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h871, hlam, p1089_1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1074, hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [hlam, hphi, ht0b, ht5b, p1089_1, u0elo4, u5ehi3]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1074, h1080, h1081, h1083, h1087, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1089_1, u3elo1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1081, h1083, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1089_1, u3elo1, u5ehi0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1074, h1081, h1083, hc02, hlam, hphi, ht23, p1089_1, u3elo1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1081, h1083, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1089_1, u3elo1, u5ehi3]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1081, h1083, h1087, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1089_1, u3elo1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1077, h1080, h1087, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1089_1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1080, hlam, p1089_1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1080, h1081, h1083, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1089_1, u3elo1, u5ehi3]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1080, h1081, h1083, h1087, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1089_1, u3elo1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1076, hlam, p1089_1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1082, hlam, p1089_1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1085, hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1087, hlam, p1089_1]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1077, hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1083, hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1086, hlam, p1089_0]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [h1077, hlam, hphi, ht0b, ht5b, p1089_1, u0elo4, u5ehi3]
                                        · have p1089_0 := h1089c.1
                                          have p1089_1 := h1089c.2.1
                                          have p1089_2 := h1089c.2.2.1
                                          have p1089_3 := h1089c.2.2.2
                                          linarith only [hlam, p1089_0]
                                    · linarith only [h1007, h1077, h1086, hlam]
                                  · linarith only [h1076, h1085, hc23, hlam, hphi, u3elo0]
                                · linarith only [h0, h1084, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · linarith only [h1007, h1077, h1079, h1083, hlam]
                            · linarith only [h1076, h1081, h1082, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h1076, h1078, h1081, h873, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h1076, h1078, h1080, h873, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h1076, h1078, h1079, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1078, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1124 | h1124
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1128 | h1128
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1129 | h1129
                              · linarith only [h1077, h1127, h1129, h744, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1132 | h1132
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1133 | h1133
                                    · linarith only [h1125, h1129, h1133, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1135 | h1135
                                      · linarith only [h1124, h1129, h1131, h1135, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                      · rcases h5bigk with h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [hlam, p1137_0]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h871, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1074, hlam, p1137_0]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [hlam, hphi, ht0b, ht5b, p1137_1, u0elo4, u5ehi3]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1077, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1128, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1137_1, u3elo1, u5ehi0]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [hlam, p1137_0]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1128, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1137_1, u3elo1, u5ehi2]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1128, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1137_1, u3elo1, u5ehi3]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1129, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1076, h1126, hc12, hlam, hphi, ht01, ht0b, ht5b, p1137_1, u5ehi3]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1126, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [hlam, p1137_0]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1126, h1128, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1137_1, u3elo1, u5ehi3]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1133, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1076, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1128, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1132, hlam, p1137_0]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [hlam, p1137_0]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h1135, hlam, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          rcases p1137_3 (m.d 0 5) (by simp) with h1158 | h1158
                                          · linarith only [h1077, h1158, hlam]
                                          · rcases p1137_3 (m.d 1 5) (by simp) with h1160 | h1160
                                            · linarith only [h1129, h1160, hlam]
                                            · linarith only [h1160, h871, hlam]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h871, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [h0, h1074, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1137_1]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          rcases p1137_3 (m.d 0 5) (by simp) with h1165 | h1165
                                          · linarith only [h1077, h1165, hlam]
                                          · linarith only [h1076, h1165, hlam]
                                        · have p1137_0 := h1137c.1
                                          have p1137_1 := h1137c.2.1
                                          have p1137_2 := h1137c.2.2.1
                                          have p1137_3 := h1137c.2.2.2
                                          linarith only [hlam, p1137_0]
                                  · linarith only [h1076, h1132, hc23, hlam, hphi, u3elo0]
                                · linarith only [h1076, h1131, h873, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                            · linarith only [h1076, h1124, h1128, h873, hlam]
                          · linarith only [h1076, h1124, h1127, h873, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h1076, h1124, h1126, h873, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h1076, h1124, h1125, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1124, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1176 | h1176
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1177 | h1177
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1178 | h1178
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1179 | h1179
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1180 | h1180
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1181 | h1181
                            · linarith only [h1076, h1181, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1181, h408, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h1177, h1180, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1007, h1176, h1178, h1179, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1177, h1178, h873, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1177, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1188 | h1188
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1189 | h1189
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1190 | h1190
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1191 | h1191
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1192 | h1192
                            · linarith only [h0, h1076, h1192, h873, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h1192, h408, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h1188, h1191, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1188, h1190, h873, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1188, h1189, h873, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1188, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
