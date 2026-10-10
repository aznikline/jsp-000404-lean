import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB1_H_I_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4bigk := hb4.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h3 | h3
    · rcases p0_3 (m.d 1 4) (by simp) with h4 | h4
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
              · rcases m.htr 0 1 4 (by decide) (by decide) with h11 | h11
                · linarith only [h11, h4, hlam]
                · linarith only [h10, h11, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h4, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
                    · linarith only [h17, h7, hlam]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                        · linarith only [h17, h20, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h10, h20, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h19, h8, hlam, p0_1]
                  · linarith only [h16, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h25 | h25
            · linarith only [h25, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h27 | h27
              · rcases m.htr 0 1 4 (by decide) (by decide) with h28 | h28
                · linarith only [h28, h4, hlam]
                · linarith only [h27, h28, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h31 | h31
                · linarith only [h31, h4, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                              · linarith only [h34, h39, hc03, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                              · linarith only [h25, h39, hlam]
                            · linarith only [h38, h7, hlam]
                          · linarith only [h31, h37, hc24, hc45, hlam, hphi, p0_1]
                        · linarith only [h27, h36, h7, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                      · linarith only [h25, h35, hlam, p0_1]
                    · linarith only [h34, h7, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h33, hlam, p0_0]
      · linarith only [h4, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
    · linarith only [h3, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h50 | h50
    · rcases p0_3 (m.d 1 4) (by simp) with h51 | h51
      · rcases p0_3 (m.d 2 4) (by simp) with h52 | h52
        · rcases p0_3 (m.d 3 4) (by simp) with h53 | h53
          · linarith only [h53, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h55 | h55
            · linarith only [h55, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h57 | h57
              · rcases m.htr 0 1 4 (by decide) (by decide) with h58 | h58
                · linarith only [h51, h58, hlam]
                · linarith only [h57, h58, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h61 | h61
                · linarith only [h51, h61, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h63 | h63
                  · linarith only [h52, h63, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                                · linarith only [h63, h69, h71, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                                · linarith only [h55, h71, hlam]
                              · linarith only [h63, h70, hc34, hc45, hlam, hphi, p0_1]
                            · linarith only [h65, h69, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                          · linarith only [h55, h63, h68, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                        · linarith only [h57, h63, h67, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h55, h66, hlam, p0_1]
                    · linarith only [h65, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h80 | h80
          · linarith only [h80, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h82 | h82
            · linarith only [h52, h82, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h84 | h84
              · rcases m.htr 0 1 4 (by decide) (by decide) with h85 | h85
                · linarith only [h51, h85, hlam]
                · linarith only [h84, h85, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
                · linarith only [h51, h88, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                            · linarith only [h52, h95, hlam]
                            · linarith only [h90, h95, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                          · linarith only [h82, h88, h94, hlam, p0_1]
                        · linarith only [h84, h91, h93, hlam, p0_1]
                      · linarith only [h82, h92, hlam, p0_1]
                    · linarith only [h91, hlam, p0_0]
                  · linarith only [h52, h90, hc02, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
      · linarith only [h51, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
    · linarith only [h50, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h105 | h105
    · rcases p0_3 (m.d 1 4) (by simp) with h106 | h106
      · rcases p0_3 (m.d 2 4) (by simp) with h107 | h107
        · rcases p0_3 (m.d 3 4) (by simp) with h108 | h108
          · rcases p0_3 (m.d 4 5) (by simp) with h109 | h109
            · linarith only [h109, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h111 | h111
              · rcases m.htr 0 1 4 (by decide) (by decide) with h112 | h112
                · linarith only [h106, h112, hlam]
                · linarith only [h111, h112, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h115 | h115
                · linarith only [h106, h115, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h117 | h117
                  · linarith only [h107, h117, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h119 | h119
                    · linarith only [h108, h119, hlam]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                        · linarith only [h119, h122, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                        · linarith only [h111, h122, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h121, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h126, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h128 | h128
              · rcases m.htr 0 1 4 (by decide) (by decide) with h129 | h129
                · linarith only [h106, h129, hlam]
                · linarith only [h128, h129, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h132 | h132
                · linarith only [h106, h132, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h134 | h134
                  · linarith only [h107, h134, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                                · linarith only [h108, h142, hlam]
                                · linarith only [h136, h142, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                              · linarith only [h134, h141, hlam, p0_1]
                            · linarith only [h108, h140, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                          · linarith only [h134, h139, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                        · linarith only [h108, h128, h134, h138, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                      · linarith only [h137, hlam, p0_0]
                    · linarith only [h108, h128, h134, h136, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
        · rcases p0_3 (m.d 3 4) (by simp) with h151 | h151
          · rcases p0_3 (m.d 4 5) (by simp) with h152 | h152
            · linarith only [h152, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 1 4 (by decide) (by decide) with h155 | h155
                · linarith only [h106, h155, hlam]
                · linarith only [h154, h155, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h158 | h158
                · linarith only [h106, h158, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
                    · linarith only [h151, h161, hlam]
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h163 | h163
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h164 | h164
                        · linarith only [h107, h161, h164, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h154, h164, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h163, hlam, p0_0]
                  · linarith only [h107, h160, hc02, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h169, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h171 | h171
              · rcases m.htr 0 1 4 (by decide) (by decide) with h172 | h172
                · linarith only [h106, h172, hlam]
                · linarith only [h171, h172, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h175 | h175
                · linarith only [h106, h175, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 0 4 5 (by decide) (by decide) with h179 | h179
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                              · linarith only [h107, h183, hlam]
                              · linarith only [h171, h178, h182, h183, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                            · linarith only [h151, h171, h178, h182, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
                          · linarith only [h171, h178, h181, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                        · linarith only [h151, h171, h178, h180, hlam, p0_1]
                      · linarith only [h179, hlam, p0_0]
                    · linarith only [h151, h177, h178, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                  · linarith only [h107, h175, h177, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
      · linarith only [h106, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
    · linarith only [h105, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h194 | h194
    · linarith only [h194, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h196 | h196
      · rcases p0_3 (m.d 2 4) (by simp) with h197 | h197
        · rcases p0_3 (m.d 3 4) (by simp) with h198 | h198
          · rcases p0_3 (m.d 4 5) (by simp) with h199 | h199
            · linarith only [h199, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h201 | h201
              · rcases m.htr 0 1 4 (by decide) (by decide) with h202 | h202
                · linarith only [h202, hlam, p0_0]
                · linarith only [h201, h202, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h205 | h205
                · linarith only [h205, hlam, p0_0]
                · linarith only [h198, h205, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h208 | h208
            · linarith only [h208, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h210 | h210
              · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
                · linarith only [h211, hlam, p0_0]
                · linarith only [h210, h211, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h214 | h214
                · linarith only [h214, hlam, p0_0]
                · linarith only [h197, h214, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
        · rcases p0_3 (m.d 3 4) (by simp) with h217 | h217
          · rcases p0_3 (m.d 4 5) (by simp) with h218 | h218
            · linarith only [h218, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h220 | h220
              · rcases m.htr 0 1 4 (by decide) (by decide) with h221 | h221
                · linarith only [h221, hlam, p0_0]
                · linarith only [h220, h221, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h224 | h224
                · linarith only [h224, hlam, p0_0]
                · linarith only [h217, h224, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h227 | h227
            · linarith only [h227, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h229 | h229
              · rcases m.htr 0 1 4 (by decide) (by decide) with h230 | h230
                · linarith only [h230, hlam, p0_0]
                · linarith only [h229, h230, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h233 | h233
                · linarith only [h233, hlam, p0_0]
                · linarith only [h233, hc14, hlam, hphi, p0_1, u1ehi0]
      · linarith only [h196, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h238 | h238
    · rcases p0_3 (m.d 1 4) (by simp) with h239 | h239
      · rcases p0_3 (m.d 2 4) (by simp) with h240 | h240
        · linarith only [h240, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h242 | h242
          · rcases p0_3 (m.d 4 5) (by simp) with h243 | h243
            · linarith only [h243, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h245 | h245
              · rcases m.htr 0 1 4 (by decide) (by decide) with h246 | h246
                · linarith only [h246, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h238, h246, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h249 | h249
                · linarith only [h249, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h238, h249, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h252 | h252
            · linarith only [h252, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h254 | h254
              · rcases m.htr 0 1 4 (by decide) (by decide) with h255 | h255
                · linarith only [h255, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h238, h255, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h258 | h258
                · linarith only [h258, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h238, h258, hlam]
      · linarith only [h239, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h262 | h262
      · rcases p0_3 (m.d 2 4) (by simp) with h263 | h263
        · linarith only [h263, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h265 | h265
          · rcases p0_3 (m.d 4 5) (by simp) with h266 | h266
            · linarith only [h266, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h268 | h268
              · rcases m.htr 0 1 4 (by decide) (by decide) with h269 | h269
                · linarith only [h269, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h265, h268, h269, hc34, hlam, hphi, ht12, ht23, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h272 | h272
                · linarith only [h268, h272, hc13, hlam, hphi, u1ehi3]
                · linarith only [h238, h265, h272, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h275 | h275
            · linarith only [h238, h275, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h277 | h277
              · rcases m.htr 0 1 4 (by decide) (by decide) with h278 | h278
                · linarith only [h238, h278, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h277, h278, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h281 | h281
                · linarith only [h277, h281, hc13, hlam, hphi, u1ehi3]
                · linarith only [h238, h281, hc14, hlam, hphi, p0_1, u1ehi0]
      · linarith only [h262, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h285 | h285
    · rcases p0_3 (m.d 1 4) (by simp) with h286 | h286
      · rcases p0_3 (m.d 2 4) (by simp) with h287 | h287
        · rcases p0_3 (m.d 3 4) (by simp) with h288 | h288
          · linarith only [h288, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h290 | h290
            · linarith only [h290, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h292 | h292
              · rcases m.htr 0 1 4 (by decide) (by decide) with h293 | h293
                · linarith only [h293, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h285, h293, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h296 | h296
                · linarith only [h296, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h285, h296, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h299 | h299
          · linarith only [h299, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h301 | h301
            · linarith only [h301, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h303 | h303
              · rcases m.htr 0 1 4 (by decide) (by decide) with h304 | h304
                · linarith only [h304, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h285, h304, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h307 | h307
                · linarith only [h307, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h285, h307, hlam]
      · linarith only [h286, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h311 | h311
      · rcases p0_3 (m.d 2 4) (by simp) with h312 | h312
        · rcases p0_3 (m.d 3 4) (by simp) with h313 | h313
          · linarith only [h313, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h315 | h315
            · linarith only [h315, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h317 | h317
              · rcases m.htr 0 1 4 (by decide) (by decide) with h318 | h318
                · linarith only [h318, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h312, h317, h318, hc24, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h321 | h321
                · linarith only [h317, h321, hc13, hlam, hphi, u1ehi3]
                · linarith only [h285, h312, h321, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
        · rcases p0_3 (m.d 3 4) (by simp) with h324 | h324
          · linarith only [h324, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h326 | h326
            · linarith only [h285, h326, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h328 | h328
              · rcases m.htr 0 1 4 (by decide) (by decide) with h329 | h329
                · linarith only [h285, h329, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h328, h329, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h332 | h332
                · linarith only [h328, h332, hc13, hlam, hphi, u1ehi3]
                · linarith only [h285, h332, hc14, hlam, hphi, p0_1, u1ehi0]
      · linarith only [h311, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h336 | h336
    · rcases p0_3 (m.d 1 4) (by simp) with h337 | h337
      · rcases p0_3 (m.d 2 4) (by simp) with h338 | h338
        · rcases p0_3 (m.d 3 4) (by simp) with h339 | h339
          · rcases p0_3 (m.d 4 5) (by simp) with h340 | h340
            · linarith only [h340, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h342 | h342
              · rcases m.htr 0 1 4 (by decide) (by decide) with h343 | h343
                · linarith only [h343, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                · linarith only [h336, h343, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h346 | h346
                · linarith only [h346, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                · linarith only [h336, h346, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h349 | h349
            · linarith only [h349, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h351 | h351
              · rcases m.htr 0 1 4 (by decide) (by decide) with h352 | h352
                · linarith only [h339, h352, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h336, h352, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h355 | h355
                · linarith only [h339, h355, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h336, h355, hlam]
        · rcases p0_3 (m.d 3 4) (by simp) with h358 | h358
          · rcases p0_3 (m.d 4 5) (by simp) with h359 | h359
            · linarith only [h359, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h361 | h361
              · rcases m.htr 0 1 4 (by decide) (by decide) with h362 | h362
                · linarith only [h338, h362, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h336, h362, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h365 | h365
                · linarith only [h338, h365, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h336, h365, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h368 | h368
            · linarith only [h368, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h370 | h370
              · rcases m.htr 0 1 4 (by decide) (by decide) with h371 | h371
                · linarith only [h338, h371, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h336, h371, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h374 | h374
                · linarith only [h338, h374, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h336, h374, hlam]
      · linarith only [h337, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h378 | h378
      · rcases p0_3 (m.d 2 4) (by simp) with h379 | h379
        · rcases p0_3 (m.d 3 4) (by simp) with h380 | h380
          · rcases p0_3 (m.d 4 5) (by simp) with h381 | h381
            · linarith only [h381, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h383 | h383
              · rcases m.htr 0 1 4 (by decide) (by decide) with h384 | h384
                · linarith only [h336, h384, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h383, h384, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h387 | h387
                · linarith only [h336, h387, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h336, h387, hc14, hlam, hphi, p0_1, u1ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h390 | h390
            · linarith only [h390, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 1 4 (by decide) (by decide) with h393 | h393
                · linarith only [h336, h393, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h392, h393, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h396 | h396
                · linarith only [h392, h396, hc13, hlam, hphi, u1ehi3]
                · linarith only [h336, h379, h396, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
        · rcases p0_3 (m.d 3 4) (by simp) with h399 | h399
          · rcases p0_3 (m.d 4 5) (by simp) with h400 | h400
            · linarith only [h400, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h402 | h402
              · rcases m.htr 0 1 4 (by decide) (by decide) with h403 | h403
                · linarith only [h336, h403, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h402, h403, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h406 | h406
                · linarith only [h402, h406, hc13, hlam, hphi, u1ehi3]
                · linarith only [h336, h399, h406, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h409 | h409
            · linarith only [h409, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h411 | h411
              · rcases m.htr 0 1 4 (by decide) (by decide) with h412 | h412
                · linarith only [h336, h412, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h411, h412, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h415 | h415
                · linarith only [h411, h415, hc13, hlam, hphi, u1ehi3]
                · linarith only [h336, h415, hc14, hlam, hphi, p0_1, u1ehi0]
      · linarith only [h378, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h419 | h419
    · linarith only [h419, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h421 | h421
      · rcases p0_3 (m.d 2 4) (by simp) with h422 | h422
        · rcases p0_3 (m.d 3 4) (by simp) with h423 | h423
          · rcases p0_3 (m.d 4 5) (by simp) with h424 | h424
            · linarith only [h424, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h426 | h426
              · rcases m.htr 0 1 4 (by decide) (by decide) with h427 | h427
                · linarith only [h421, h427, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h426, h427, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h430 | h430
                · linarith only [h426, h430, hc13, hlam, hphi, u1ehi3]
                · linarith only [h430, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h433 | h433
            · linarith only [h433, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h435 | h435
              · rcases m.htr 0 1 4 (by decide) (by decide) with h436 | h436
                · linarith only [h421, h436, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h435, h436, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h439 | h439
                · linarith only [h435, h439, hc13, hlam, hphi, u1ehi3]
                · linarith only [h439, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
        · linarith only [h422, hlam, p0_0]
      · linarith only [h421, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h446 | h446
    · rcases p0_3 (m.d 1 4) (by simp) with h447 | h447
      · rcases p0_3 (m.d 2 4) (by simp) with h448 | h448
        · rcases p0_3 (m.d 3 4) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h451 | h451
            · linarith only [h451, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h453 | h453
              · rcases m.htr 0 1 4 (by decide) (by decide) with h454 | h454
                · linarith only [h447, h454, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h453, h454, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h457 | h457
                · linarith only [h453, h457, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h459 | h459
                  · linarith only [h459, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h446, h459, hlam]
        · linarith only [h448, hlam, p0_0]
      · linarith only [h447, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h464 | h464
      · rcases p0_3 (m.d 2 4) (by simp) with h465 | h465
        · rcases p0_3 (m.d 3 4) (by simp) with h466 | h466
          · linarith only [h466, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · linarith only [h446, h468, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h470 | h470
              · rcases m.htr 0 1 4 (by decide) (by decide) with h471 | h471
                · linarith only [h446, h464, h471, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h470, h471, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h474 | h474
                · linarith only [h470, h474, hc13, hlam, hphi, u1ehi3]
                · linarith only [h446, h474, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
        · linarith only [h465, hlam, p0_0]
      · linarith only [h464, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h479 | h479
    · rcases p0_3 (m.d 1 4) (by simp) with h480 | h480
      · rcases p0_3 (m.d 2 4) (by simp) with h481 | h481
        · rcases p0_3 (m.d 3 4) (by simp) with h482 | h482
          · rcases p0_3 (m.d 4 5) (by simp) with h483 | h483
            · linarith only [h483, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h485 | h485
              · rcases m.htr 0 1 4 (by decide) (by decide) with h486 | h486
                · linarith only [h480, h486, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                · linarith only [h485, h486, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h489 | h489
                · linarith only [h485, h489, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h491 | h491
                  · linarith only [h491, hc02, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                  · linarith only [h479, h491, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h494 | h494
            · linarith only [h494, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h496 | h496
              · rcases m.htr 0 1 4 (by decide) (by decide) with h497 | h497
                · linarith only [h480, h482, h497, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h496, h497, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h500 | h500
                · linarith only [h496, h500, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h502 | h502
                  · linarith only [h482, h502, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h479, h502, hlam]
        · linarith only [h481, hlam, p0_0]
      · linarith only [h480, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h507 | h507
      · rcases p0_3 (m.d 2 4) (by simp) with h508 | h508
        · rcases p0_3 (m.d 3 4) (by simp) with h509 | h509
          · rcases p0_3 (m.d 4 5) (by simp) with h510 | h510
            · linarith only [h510, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h512 | h512
              · rcases m.htr 0 1 4 (by decide) (by decide) with h513 | h513
                · linarith only [h479, h507, h513, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h512, h513, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h516 | h516
                · linarith only [h512, h516, hc13, hlam, hphi, u1ehi3]
                · linarith only [h479, h516, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
          · rcases p0_3 (m.d 4 5) (by simp) with h519 | h519
            · linarith only [h519, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h521 | h521
              · rcases m.htr 0 1 4 (by decide) (by decide) with h522 | h522
                · linarith only [h479, h507, h522, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h521, h522, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h525 | h525
                · linarith only [h521, h525, hc13, hlam, hphi, u1ehi3]
                · linarith only [h479, h525, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
        · linarith only [h508, hlam, p0_0]
      · linarith only [h507, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h530 | h530
    · linarith only [h530, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h532 | h532
      · rcases p0_3 (m.d 2 4) (by simp) with h533 | h533
        · rcases p0_3 (m.d 3 4) (by simp) with h534 | h534
          · rcases p0_3 (m.d 4 5) (by simp) with h535 | h535
            · linarith only [h535, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h537 | h537
              · rcases m.htr 0 1 4 (by decide) (by decide) with h538 | h538
                · linarith only [h532, h538, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h537, h538, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h541 | h541
                · linarith only [h537, h541, hc13, hlam, hphi, u1ehi3]
                · linarith only [h541, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · linarith only [h534, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h545 | h545
          · rcases p0_3 (m.d 4 5) (by simp) with h546 | h546
            · linarith only [h546, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h548 | h548
              · rcases m.htr 0 1 4 (by decide) (by decide) with h549 | h549
                · linarith only [h532, h549, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h548, h549, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h552 | h552
                · linarith only [h548, h552, hc13, hlam, hphi, u1ehi3]
                · linarith only [h552, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · linarith only [h545, hlam, p0_0]
      · linarith only [h532, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h558 | h558
    · rcases p0_3 (m.d 1 4) (by simp) with h559 | h559
      · rcases p0_3 (m.d 2 4) (by simp) with h560 | h560
        · linarith only [h560, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h562 | h562
          · rcases p0_3 (m.d 4 5) (by simp) with h563 | h563
            · linarith only [h563, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h565 | h565
              · rcases m.htr 0 1 4 (by decide) (by decide) with h566 | h566
                · linarith only [h559, h566, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h565, h566, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h569 | h569
                · linarith only [h565, h569, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h571 | h571
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h572 | h572
                    · linarith only [h572, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h558, h572, hlam]
                  · linarith only [h571, hc02, hc34, hlam, hphi, ht23, p0_1]
          · linarith only [h562, hlam, p0_0]
      · linarith only [h559, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h578 | h578
      · rcases p0_3 (m.d 2 4) (by simp) with h579 | h579
        · linarith only [h579, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h581 | h581
          · rcases p0_3 (m.d 4 5) (by simp) with h582 | h582
            · linarith only [h558, h582, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h584 | h584
              · rcases m.htr 0 1 4 (by decide) (by decide) with h585 | h585
                · linarith only [h558, h578, h585, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h584, h585, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h588 | h588
                · linarith only [h584, h588, hc13, hlam, hphi, u1ehi3]
                · linarith only [h558, h588, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · linarith only [h581, hlam, p0_0]
      · linarith only [h578, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h594 | h594
    · rcases p0_3 (m.d 1 4) (by simp) with h595 | h595
      · rcases p0_3 (m.d 2 4) (by simp) with h596 | h596
        · rcases p0_3 (m.d 3 4) (by simp) with h597 | h597
          · rcases p0_3 (m.d 4 5) (by simp) with h598 | h598
            · linarith only [h598, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h600 | h600
              · rcases m.htr 0 1 4 (by decide) (by decide) with h601 | h601
                · linarith only [h595, h601, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                · linarith only [h600, h601, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h604 | h604
                · linarith only [h600, h604, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h606 | h606
                  · linarith only [h596, h606, hc02, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h608 | h608
                    · linarith only [h600, h608, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1]
                    · linarith only [h594, h608, hlam]
          · linarith only [h597, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h612 | h612
          · rcases p0_3 (m.d 4 5) (by simp) with h613 | h613
            · linarith only [h613, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h615 | h615
              · rcases m.htr 0 1 4 (by decide) (by decide) with h616 | h616
                · linarith only [h595, h596, h616, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h615, h616, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h619 | h619
                · linarith only [h615, h619, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h622 | h622
                    · linarith only [h596, h615, h622, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                    · linarith only [h594, h622, hlam]
                  · linarith only [h596, h621, hc02, hc34, hlam, hphi, ht23, p0_1]
          · linarith only [h612, hlam, p0_0]
      · linarith only [h595, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h628 | h628
      · rcases p0_3 (m.d 2 4) (by simp) with h629 | h629
        · rcases p0_3 (m.d 3 4) (by simp) with h630 | h630
          · rcases p0_3 (m.d 4 5) (by simp) with h631 | h631
            · linarith only [h631, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h633 | h633
              · rcases m.htr 0 1 4 (by decide) (by decide) with h634 | h634
                · linarith only [h594, h628, h634, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h633, h634, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h637 | h637
                · linarith only [h633, h637, hc13, hlam, hphi, u1ehi3]
                · linarith only [h594, h629, h637, hc24, hlam, hphi, ht12, p0_1, u1ehi0]
          · linarith only [h630, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h641 | h641
          · rcases p0_3 (m.d 4 5) (by simp) with h642 | h642
            · linarith only [h642, hlam, p0_0]
            · rcases m.htr 0 1 3 (by decide) (by decide) with h644 | h644
              · rcases m.htr 0 1 4 (by decide) (by decide) with h645 | h645
                · linarith only [h594, h628, h645, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h644, h645, hc14, hlam, hphi, u1ehi2]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h648 | h648
                · linarith only [h644, h648, hc13, hlam, hphi, u1ehi3]
                · linarith only [h594, h648, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi0]
          · linarith only [h641, hlam, p0_0]
      · linarith only [h628, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB1_H_I_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h1elo := hb1.1
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
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h0, h10, h12, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h11, hc14, hlam, hphi, ht45, u5elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                          · linarith only [h0, h10, h17, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h1, h10, h19, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h19, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h16, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h4, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                              · linarith only [h0, h25, h31, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · linarith only [h29, h31, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h30, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h1, h25, h29, h5, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h28, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1, h25, h27, h5, h7, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h25, h26, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h0, h25, h39, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h39, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h6, hc04, hlam, hphi, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                      · linarith only [h1, h47, h5, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                          · linarith only [h0, h44, h5, h50, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                            · linarith only [h0, h44, h52, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h52, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h47, h49, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h46, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h4, h44, h45, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                      · linarith only [h1, h5, h60, hlam]
                      · linarith only [h44, h58, h60, hlam]
                    · linarith only [h59, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h0, h4, h58, h64, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h64, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h43, hc04, hlam, hphi, ht45, u5elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h68 | h68
            · rcases m.htr 0 4 5 (by decide) (by decide) with h69 | h69
              · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h0, h4, h71, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                      · linarith only [h70, h71, h74, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                          · linarith only [h70, h71, h74, h77, hlam]
                          · linarith only [h0, h1, h4, h68, h70, h77, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h76, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h70, h73, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h4, h82, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h1, h85, h90, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h90, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h4, h86, h89, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                            · linarith only [h0, h4, h84, h87, h88, hc25, hlam, hphi, u5elo3]
                          · linarith only [h1, h68, h70, h84, h87, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h86, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1, h68, h70, h84, h85, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h84, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h69, hc04, hlam, hphi, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
                  · linarith only [h0, h102, h4, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                      · linarith only [h1, h105, h68, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                          · linarith only [h0, h101, h108, h4, h68, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                            · linarith only [h0, h101, h110, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h110, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h102, h107, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h101, h104, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                  · linarith only [h101, h115, h4, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                      · linarith only [h1, h118, h68, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                                · rcases h4bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h121, h68, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h4, hlam, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h68, hlam, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h121, h68, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h2, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h115, hlam, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h118, hlam, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p125_1, u1elo3]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h0, h117, h122, h124, h4, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h115, h117, h122, h124, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h1, h101, h117, h121, h122, h124, h68, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    rcases p125_3 (m.d 0 4) (by simp) with h140 | h140
                                    · linarith only [h140, h4, hlam]
                                    · linarith only [h100, h140, hlam]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h1, h101, h117, h122, h124, h68, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h101, h117, h118, h122, h124, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h121, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h121, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h100, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h120, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h123, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h124, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                · linarith only [h124, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h123, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h122, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                                · rcases h4bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p159_1, u1elo0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h4, hlam, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h68, hlam, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p159_1, u1elo0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h2, hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h115, hlam, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h118, hlam, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p159_1, u1elo3]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h0, h117, h156, h158, h4, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h115, h117, h156, h158, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h121, hlam, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    rcases p159_3 (m.d 0 4) (by simp) with h174 | h174
                                    · linarith only [h174, h4, hlam]
                                    · linarith only [h100, h174, hlam]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h1, h101, h117, h156, h158, h68, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h101, h117, h118, h156, h158, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h0, h117, h156, h158, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p159_1]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    rcases p159_3 (m.d 0 4) (by simp) with h181 | h181
                                    · linarith only [h181, h68, hlam]
                                    · linarith only [h100, h181, hlam]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h100, hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h120, hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h157, hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [h158, hlam, p159_0]
                                  · have p159_0 := h159c.1
                                    have p159_1 := h159c.2.1
                                    have p159_2 := h159c.2.2.1
                                    have p159_3 := h159c.2.2.2
                                    linarith only [hlam, p159_0]
                                · linarith only [h158, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h120, h157, h2, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h101, h117, h156, hc25, hlam, hphi, u5elo3]
                        · linarith only [h118, h120, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h117, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h100, hc04, hlam, hphi, ht45, u5elo4]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h196 | h196
        · rcases m.htr 0 2 4 (by decide) (by decide) with h197 | h197
          · linarith only [h0, h197, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h199 | h199
            · linarith only [h1, h199, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
              · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                · linarith only [h0, h2, h202, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
                  · linarith only [h1, h2, h202, h204, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                    · linarith only [h0, h2, h206, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                    · linarith only [h206, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h2, h201, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · linarith only [h0, h196, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
      · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 0 2 4 (by decide) (by decide) with h213 | h213
          · rcases m.htr 0 3 4 (by decide) (by decide) with h214 | h214
            · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
              · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
                · linarith only [h0, h1, h216, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
                  · linarith only [h0, h1, h218, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · linarith only [h0, h1, h213, h218, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · linarith only [h215, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h1, h211, h214, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
            · rcases m.htr 0 4 5 (by decide) (by decide) with h224 | h224
              · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
                · linarith only [h0, h1, h225, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
                  · linarith only [h0, h1, h213, h227, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
                    · linarith only [h0, h1, h229, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · linarith only [h229, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h224, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h1, h211, h223, hlam]
        · linarith only [h212, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h235 | h235
        · rcases m.htr 0 2 4 (by decide) (by decide) with h236 | h236
          · linarith only [h0, h211, h236, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h238 | h238
            · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
              · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                · linarith only [h0, h1, h240, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h242 | h242
                  · linarith only [h0, h1, h236, h242, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h244 | h244
                    · linarith only [h0, h1, h244, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · linarith only [h244, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h211, h239, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h248 | h248
              · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
                · linarith only [h0, h1, h249, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h251 | h251
                  · linarith only [h0, h1, h251, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h253 | h253
                    · linarith only [h0, h1, h253, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · linarith only [h253, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h1, h238, h248, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · linarith only [h0, h235, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h258 | h258
    · rcases m.htr 0 1 4 (by decide) (by decide) with h259 | h259
      · rcases m.htr 0 1 5 (by decide) (by decide) with h260 | h260
        · rcases m.htr 0 2 4 (by decide) (by decide) with h261 | h261
          · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
            · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
              · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                · rcases m.htr 1 2 4 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h266 | h266
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h267 | h267
                      · linarith only [h0, h258, h267, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h258, h262, h267, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h266, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h258, h261, h264, h265, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h258, h264, hlam]
              · linarith only [h263, hc04, hlam, hphi, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
              · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                      · linarith only [h258, h262, h278, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                        · linarith only [h0, h259, h280, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h276, h280, hc24, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h277, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h258, h261, h275, h276, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h258, h275, hlam]
              · linarith only [h274, hc04, hlam, hphi, ht45, u5elo4]
          · linarith only [h0, h259, h261, hlam]
        · linarith only [h260, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h289 | h289
        · rcases m.htr 0 2 4 (by decide) (by decide) with h290 | h290
          · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
            · linarith only [h258, h259, h291, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
              · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h296 | h296
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h297 | h297
                      · linarith only [h258, h259, h291, h295, h297, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h299 | h299
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                          · linarith only [h259, h294, h297, h300, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h302 | h302
                            · linarith only [h258, h259, h294, h295, h302, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h302, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h258, h259, h299, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h259, h295, h296, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h258, h290, h294, h295, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h258, h294, hlam]
              · linarith only [h259, h293, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h310 | h310
            · linarith only [h0, h258, h290, h310, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
              · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
                  · linarith only [h0, h258, h290, h313, h314, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
                      · linarith only [h258, h310, h317, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                          · linarith only [h0, h313, h314, h317, h320, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h258, h313, h314, h320, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h258, h313, h314, h319, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h258, h313, h316, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h0, h258, h313, hlam]
              · linarith only [h290, h312, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h258, h289, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h328 | h328
      · rcases m.htr 0 1 5 (by decide) (by decide) with h329 | h329
        · rcases m.htr 0 2 4 (by decide) (by decide) with h330 | h330
          · rcases m.htr 0 3 4 (by decide) (by decide) with h331 | h331
            · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
              · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
                · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h337 | h337
                        · linarith only [h258, h328, h333, h337, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h337, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h258, h328, h331, h334, h336, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h258, h328, h333, h334, h335, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h330, h334, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h346 | h346
                        · linarith only [h0, h328, h333, h346, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h346, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h258, h331, h345, hlam]
                    · linarith only [h0, h328, h343, h344, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h330, h343, hlam]
              · linarith only [h332, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h258, h328, h331, hlam]
          · linarith only [h0, h328, h330, hlam]
        · linarith only [h329, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h356 | h356
        · rcases m.htr 0 2 4 (by decide) (by decide) with h357 | h357
          · rcases m.htr 0 3 4 (by decide) (by decide) with h358 | h358
            · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
              · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h366 | h366
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
                                · linarith only [h360, h365, h368, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h368, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h328, h356, h364, h367, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                            · linarith only [h366, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
                            · linarith only [h258, h358, h360, h365, h373, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h373, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h328, h364, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h258, h358, h363, hlam]
                    · linarith only [h0, h362, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h357, h361, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h383 | h383
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h384 | h384
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h386 | h386
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h387 | h387
                                · rcases h4bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h328, hlam, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h328, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p388_1, u1elo3]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h357, h360, h387, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h357, h360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p388_1, u1elo3]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h360, h380, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h360, h380, h387, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h360, h380, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h357, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h380, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h387, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h0, h357, h360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h358, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h382, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h384, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h358, hc03, hc45, hlam, hphi, ht0b, ht5b, p388_1]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h359, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h383, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h386, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [h387, hlam, p388_0]
                                  · have p388_0 := h388c.1
                                    have p388_1 := h388c.2.1
                                    have p388_2 := h388c.2.2.1
                                    have p388_3 := h388c.2.2.2
                                    linarith only [hlam, p388_0]
                                · linarith only [h387, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h383, h386, hc24, hlam, hphi, ht45, u5elo1]
                            · linarith only [h328, h360, h380, h385, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h328, h356, h360, h380, h383, h384, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h328, h356, h381, h383, hc25, hlam, hphi, u5elo4]
                      · linarith only [h258, h358, h382, hlam]
                    · linarith only [h328, h380, h381, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h356, h357, h380, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h328, h356, h359, hc15, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h423 | h423
              · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
                · rcases m.htr 1 2 4 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h426 | h426
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                      · linarith only [h258, h356, h358, h424, h426, h427, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                          · linarith only [h424, h427, h430, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h434 | h434
                                · rcases h4bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h328, hlam, p435_1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h258, h328, h356, h426, h427, h430, h432, h434, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p435_1, u1elo3]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h358, hlam, p435_1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h0, h357, hc45, hlam, hphi, ht01, ht0b, ht5b, p435_1, u1elo1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p435_1, u1elo3]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h258, h356, h425, h426, h427, h430, h432, h434, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p435_1, u1elo1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h427, hlam, p435_1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h425, hc45, hlam, hphi, ht01, ht0b, ht5b, p435_1, u1elo1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h357, hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h425, hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h430, hlam, p435_1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h0, h357, hc45, hlam, hphi, ht01, ht0b, ht5b, p435_1, u1elo1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h328, h356, h426, h432, h434, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p435_1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h328, h356, h426, h432, h434, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p435_1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h430, h432, h434, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p435_1]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    rcases p435_3 (m.d 0 4) (by simp) with h455 | h455
                                    · linarith only [h358, h455, hlam]
                                    · linarith only [h423, h455, hlam]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h423, hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h429, hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h433, hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [h434, hlam, p435_0]
                                  · have p435_0 := h435c.1
                                    have p435_1 := h435c.2.1
                                    have p435_2 := h435c.2.2.1
                                    have p435_3 := h435c.2.2.2
                                    linarith only [hlam, p435_0]
                                · linarith only [h434, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h258, h356, h425, h427, h429, h430, h433, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · linarith only [h432, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h258, h356, h426, h427, h429, hc25, hlam, hphi, u5elo4]
                    · linarith only [h258, h424, h426, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h258, h356, h357, h424, h425, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                      · linarith only [h258, h356, h358, h470, h471, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h424, h469, h471, hlam]
                    · linarith only [h0, h470, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h357, h469, hlam]
              · linarith only [h358, h423, hc03, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h477 | h477
            · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
              · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                · rcases m.htr 1 2 4 (by decide) (by decide) with h480 | h480
                  · linarith only [h0, h356, h357, h480, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                      · linarith only [h479, h480, h483, hlam]
                      · linarith only [h258, h477, h483, hlam]
                    · linarith only [h258, h479, h482, hc03, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h487 | h487
                  · linarith only [h0, h357, h487, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h489 | h489
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h490 | h490
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h495 | h495
                                · rcases h4bigk with h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h328, hlam, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h357, hlam, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h495, hc04, hc45, hlam, hphi, ht0b, ht5b, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h328, h490, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo2]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h490, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p496_1, u1elo2]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h487, hlam, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h490, h495, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo2]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h490, hc45, hlam, hphi, ht01, ht0b, ht5b, p496_1, u1elo2]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h0, h356, h357, h489, h492, h493, h495, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h487, h492, hc12, hc23, hlam, hphi, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h492, h495, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    rcases p496_3 (m.d 0 4) (by simp) with h511 | h511
                                    · linarith only [h357, h511, hlam]
                                    · linarith only [h478, h511, hlam]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h477, hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h490, hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h492, hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h477, hc03, hc45, hlam, hphi, ht0b, ht5b, p496_1]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h478, hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h491, hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h494, hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [h495, hlam, p496_0]
                                  · have p496_0 := h496c.1
                                    have p496_1 := h496c.2.1
                                    have p496_2 := h496c.2.2.1
                                    have p496_3 := h496c.2.2.2
                                    linarith only [hlam, p496_0]
                                · linarith only [h495, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h356, h487, h491, h494, hlam]
                            · linarith only [h0, h487, h492, h493, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h356, h479, h489, h492, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h491, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h258, h328, h356, h477, h489, h490, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                    · linarith only [h0, h489, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h478, hc04, hlam, hphi, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
              · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
                  · linarith only [h0, h356, h357, h534, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h536 | h536
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h537 | h537
                      · linarith only [h258, h356, h477, h536, h537, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                          · linarith only [h533, h534, h537, h540, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h542 | h542
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h543 | h543
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h544 | h544
                                · rcases h4bigk with h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h328, hlam, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h357, hlam, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h477, hlam, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h328, hc45, hlam, hphi, ht01, ht0b, ht5b, p545_1, u1elo3]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1, u1elo3]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h534, hlam, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h537, hlam, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p545_1, u1elo3]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h0, h356, h357, h536, h540, h542, h544, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h328, h356, h536, h540, h542, h544, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h540, hlam, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    rcases p545_3 (m.d 0 4) (by simp) with h560 | h560
                                    · linarith only [h357, h560, hlam]
                                    · linarith only [h532, h560, hlam]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h0, h356, h357, h536, h542, h544, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h534, hc12, hc34, hlam, hphi, ht23, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h0, h356, h357, h536, h542, h544, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p545_1]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    rcases p545_3 (m.d 0 4) (by simp) with h567 | h567
                                    · linarith only [h477, h567, hlam]
                                    · linarith only [h532, h567, hlam]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h532, hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h539, hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h543, hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [h544, hlam, p545_0]
                                  · have p545_0 := h545c.1
                                    have p545_1 := h545c.2.1
                                    have p545_2 := h545c.2.2.1
                                    have p545_3 := h545c.2.2.2
                                    linarith only [hlam, p545_0]
                                · linarith only [h544, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h258, h356, h533, h534, h539, h543, hlam]
                            · linarith only [h542, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h258, h356, h533, h534, h536, h539, hc25, hlam, hphi, u5elo4]
                    · linarith only [h258, h533, h536, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                  · linarith only [h357, h533, h580, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h582 | h582
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h583 | h583
                      · linarith only [h258, h477, h583, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h585 | h585
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h586 | h586
                          · linarith only [h0, h356, h533, h582, h583, h586, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h356, h533, h582, h586, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h328, h585, hc04, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h582, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h258, h356, h477, h532, hc15, hlam, hphi, u5elo4]
        · linarith only [h356, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sAB1_H_I_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB1_H_I_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h9 | h9
              · linarith only [h9, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h9, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h12 | h12
            · linarith only [h12, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
              · linarith only [h14, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h14, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 4 5) (by simp) with h18 | h18
            · linarith only [h18, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
              · linarith only [h20, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h20, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h23 | h23
            · linarith only [h23, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
              · linarith only [h25, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h25, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h29 | h29
    · rcases p0_3 (m.d 1 4) (by simp) with h30 | h30
      · linarith only [h30, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h35, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h37 | h37
              · linarith only [h37, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h30, h37, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h30, h40, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
              · linarith only [h30, h42, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h30, h42, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h29, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h46 | h46
    · rcases p0_3 (m.d 1 4) (by simp) with h47 | h47
      · linarith only [h47, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h49 | h49
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h52, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h54 | h54
              · linarith only [h54, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h47, h54, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h57 | h57
          · linarith only [h57, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h59 | h59
            · linarith only [h47, h59, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h61 | h61
              · linarith only [h47, h61, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h47, h61, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h46, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h65 | h65
    · rcases p0_3 (m.d 1 4) (by simp) with h66 | h66
      · linarith only [h66, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h68 | h68
        · rcases p0_3 (m.d 3 4) (by simp) with h69 | h69
          · rcases p0_3 (m.d 4 5) (by simp) with h70 | h70
            · linarith only [h70, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h72 | h72
              · linarith only [h66, h72, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h66, h72, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
              · linarith only [h69, h77, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h66, h77, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h80 | h80
          · rcases p0_3 (m.d 4 5) (by simp) with h81 | h81
            · linarith only [h81, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h83 | h83
              · linarith only [h68, h83, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h66, h83, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h86 | h86
            · linarith only [h86, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
              · linarith only [h66, h88, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h66, h88, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
    · linarith only [h65, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h97 | h97
    · linarith only [h97, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h99 | h99
      · linarith only [h99, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · rcases p0_3 (m.d 3 4) (by simp) with h102 | h102
          · rcases p0_3 (m.d 4 5) (by simp) with h103 | h103
            · linarith only [h103, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h105 | h105
              · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
                · linarith only [h106, hlam, p0_0]
                · linarith only [h102, h106, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h105, h99, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h110 | h110
            · linarith only [h110, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 2 4 (by decide) (by decide) with h113 | h113
                · linarith only [h113, hlam, p0_0]
                · linarith only [h113, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h112, h99, hlam]
        · linarith only [h101, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
    · rcases p0_3 (m.d 1 4) (by simp) with h119 | h119
      · linarith only [h119, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h121 | h121
        · rcases p0_3 (m.d 3 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h125 | h125
              · linarith only [h118, h125, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h118, h125, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h128 | h128
            · linarith only [h128, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h130 | h130
              · linarith only [h118, h130, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h118, h130, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h121, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · rcases p0_3 (m.d 3 4) (by simp) with h137 | h137
          · rcases p0_3 (m.d 4 5) (by simp) with h138 | h138
            · linarith only [h118, h138, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h140 | h140
              · linarith only [h118, h140, hlam]
              · linarith only [h137, h140, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h145 | h145
              · linarith only [h118, h145, hlam]
              · linarith only [h145, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h136, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h150 | h150
    · rcases p0_3 (m.d 1 4) (by simp) with h151 | h151
      · linarith only [h151, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h153 | h153
        · rcases p0_3 (m.d 3 4) (by simp) with h154 | h154
          · linarith only [h154, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h158 | h158
              · linarith only [h150, h158, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h150, h151, h158, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h153, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h162 | h162
      · linarith only [h150, h162, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h164 | h164
        · rcases p0_3 (m.d 3 4) (by simp) with h165 | h165
          · linarith only [h165, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h167 | h167
            · linarith only [h167, hc34, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h169 | h169
              · rcases m.htr 0 2 4 (by decide) (by decide) with h170 | h170
                · linarith only [h150, h169, h170, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h150, h170, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h162, h169, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h164, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h175 | h175
    · rcases p0_3 (m.d 1 4) (by simp) with h176 | h176
      · linarith only [h176, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h178 | h178
        · rcases p0_3 (m.d 3 4) (by simp) with h179 | h179
          · rcases p0_3 (m.d 4 5) (by simp) with h180 | h180
            · linarith only [h180, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h182 | h182
              · linarith only [h175, h176, h182, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h175, h176, h182, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h185 | h185
            · linarith only [h185, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h187 | h187
              · linarith only [h175, h179, h187, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h175, h176, h187, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
        · linarith only [h178, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h191 | h191
      · linarith only [h175, h191, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · rcases p0_3 (m.d 4 5) (by simp) with h195 | h195
            · linarith only [h195, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 2 4 (by decide) (by decide) with h198 | h198
                · linarith only [h175, h197, h198, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h175, h194, h198, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h191, h194, h197, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h202 | h202
            · linarith only [h202, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h204 | h204
              · rcases m.htr 0 2 4 (by decide) (by decide) with h205 | h205
                · linarith only [h175, h204, h205, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h175, h205, hc02, hc24, hlam, hphi, p0_1]
              · linarith only [h191, h204, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h193, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h210 | h210
    · linarith only [h210, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h212 | h212
      · linarith only [h212, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h214 | h214
        · rcases p0_3 (m.d 3 4) (by simp) with h215 | h215
          · rcases p0_3 (m.d 4 5) (by simp) with h216 | h216
            · linarith only [h216, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h218 | h218
              · rcases m.htr 0 2 4 (by decide) (by decide) with h219 | h219
                · linarith only [h214, h218, h219, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h219, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h212, h218, hlam]
          · linarith only [h215, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 4 5) (by simp) with h225 | h225
            · linarith only [h225, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h227 | h227
              · rcases m.htr 0 2 4 (by decide) (by decide) with h228 | h228
                · rcases m.htr 0 3 4 (by decide) (by decide) with h229 | h229
                  · linarith only [h229, hlam, p0_0]
                  · linarith only [h229, hc03, hc34, hlam, hphi, p0_1]
                · linarith only [h214, h228, hlam]
              · linarith only [h212, h227, hlam]
          · linarith only [h224, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h235 | h235
    · rcases p0_3 (m.d 1 4) (by simp) with h236 | h236
      · linarith only [h236, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h238 | h238
        · rcases p0_3 (m.d 3 4) (by simp) with h239 | h239
          · rcases p0_3 (m.d 4 5) (by simp) with h240 | h240
            · linarith only [h240, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h242 | h242
              · linarith only [h235, h242, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h235, h242, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h239, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h246 | h246
          · rcases p0_3 (m.d 4 5) (by simp) with h247 | h247
            · linarith only [h247, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h249 | h249
              · linarith only [h235, h249, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h235, h249, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h246, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h253 | h253
      · linarith only [h253, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h255 | h255
        · rcases p0_3 (m.d 3 4) (by simp) with h256 | h256
          · rcases p0_3 (m.d 4 5) (by simp) with h257 | h257
            · linarith only [h235, h257, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h259 | h259
              · linarith only [h235, h259, hlam]
              · linarith only [h259, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h256, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h264, hc14, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h266 | h266
              · linarith only [h235, h266, hlam]
              · linarith only [h266, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h270 | h270
    · rcases p0_3 (m.d 1 4) (by simp) with h271 | h271
      · linarith only [h271, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h273 | h273
        · linarith only [h273, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h275 | h275
          · rcases p0_3 (m.d 4 5) (by simp) with h276 | h276
            · linarith only [h276, hc24, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h278 | h278
              · linarith only [h270, h278, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h270, h271, h278, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h275, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h282 | h282
      · linarith only [h270, h282, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h284 | h284
        · linarith only [h284, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h286 | h286
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · linarith only [h270, h287, hc04, hc45, hlam, hphi, p0_1]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h289 | h289
              · rcases m.htr 0 2 4 (by decide) (by decide) with h290 | h290
                · linarith only [h270, h290, hlam]
                · linarith only [h290, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h282, h289, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h286, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h296 | h296
    · rcases p0_3 (m.d 1 4) (by simp) with h297 | h297
      · linarith only [h297, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h299 | h299
        · rcases p0_3 (m.d 3 4) (by simp) with h300 | h300
          · rcases p0_3 (m.d 4 5) (by simp) with h301 | h301
            · linarith only [h301, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h303 | h303
              · linarith only [h296, h297, h303, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h296, h297, h303, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h300, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h307 | h307
          · rcases p0_3 (m.d 4 5) (by simp) with h308 | h308
            · linarith only [h308, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h310 | h310
              · linarith only [h296, h297, h310, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h296, h297, h310, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
          · linarith only [h307, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h314 | h314
      · linarith only [h296, h314, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h316 | h316
        · rcases p0_3 (m.d 3 4) (by simp) with h317 | h317
          · rcases p0_3 (m.d 4 5) (by simp) with h318 | h318
            · linarith only [h318, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h320 | h320
              · rcases m.htr 0 2 4 (by decide) (by decide) with h321 | h321
                · linarith only [h296, h316, h320, h321, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h296, h321, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h314, h320, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h317, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h326 | h326
          · rcases p0_3 (m.d 4 5) (by simp) with h327 | h327
            · linarith only [h327, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h329 | h329
              · rcases m.htr 0 2 4 (by decide) (by decide) with h330 | h330
                · rcases m.htr 0 3 4 (by decide) (by decide) with h331 | h331
                  · linarith only [h296, h331, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h296, h331, hc03, hc34, hlam, hphi, p0_1]
                · linarith only [h316, h330, hc02, hc34, hlam, hphi, ht23, p0_1]
              · linarith only [h314, h329, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h326, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB1_H_I_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
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
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB1_M_IR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h1ehi := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h14, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h10, h11, h14, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                          · linarith only [h0, h17, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h11, h19, hc24, hlam, hphi, ht12, u1ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h10, h11, h21, hlam]
                              · rcases h4bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  rcases p23_3 (m.d 0 4) (by simp) with h25 | h25
                                  · rcases p23_3 (m.d 1 4) (by simp) with h26 | h26
                                    · linarith only [h2, h26, hlam]
                                    · rcases p23_3 (m.d 2 4) (by simp) with h28 | h28
                                      · linarith only [h28, h5, hlam]
                                      · rcases p23_3 (m.d 3 4) (by simp) with h30 | h30
                                        · linarith only [h30, h6, hlam]
                                        · rcases p23_3 (m.d 4 5) (by simp) with h32 | h32
                                          · linarith only [h32, h7, hlam]
                                          · linarith only [h11, h32, hlam]
                                  · linarith only [h2, h25, hlam]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  rcases p23_3 (m.d 0 4) (by simp) with h36 | h36
                                  · rcases p23_3 (m.d 1 4) (by simp) with h37 | h37
                                    · linarith only [h2, h37, hlam]
                                    · linarith only [h37, h9, hlam]
                                  · linarith only [h36, h5, hlam]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  rcases p23_3 (m.d 0 4) (by simp) with h41 | h41
                                  · rcases p23_3 (m.d 1 4) (by simp) with h42 | h42
                                    · linarith only [h2, h42, hlam]
                                    · linarith only [h10, h42, hlam]
                                  · linarith only [h41, h6, hlam]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h11, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p23_1, u1ehi3]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h2, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h11, hc45, hlam, hphi, p23_1, u4ehi2]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h11, h17, hc23, hc45, hlam, hphi, ht34, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h11, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h5, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h9, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h17, hlam, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h19, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h6, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h10, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi2]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h21, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h7, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h4, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h4, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi2]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h4, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi3]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                          · linarith only [h10, h68, hc23, hlam, hphi, ht12, u1ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                            · linarith only [h0, h70, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h2, h67, h70, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                          · linarith only [h0, h10, h4, h6, h67, h7, h73, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                            · linarith only [h10, h67, h75, hc24, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                              · linarith only [h10, h67, h77, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                              · linarith only [h0, h10, h4, h6, h7, h77, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h5, h8, h80, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                          · linarith only [h0, h5, h8, h80, h83, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                              · rcases h4bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h4, h6, h82, hc01, hlam, hphi, ht0b, ht45, ht5b, p87_1, u4ehi4]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h4, h6, h80, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p87_1, u1ehi2]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  rcases p87_3 (m.d 0 4) (by simp) with h92 | h92
                                  · rcases p87_3 (m.d 1 4) (by simp) with h93 | h93
                                    · linarith only [h2, h93, hlam]
                                    · linarith only [h82, h93, hlam]
                                  · linarith only [h92, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h2, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h9, hlam, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h80, hlam, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p87_1, u4ehi4]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h5, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht12, p87_1, u1ehi3]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h83, hlam, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h4, h6, h83, hc01, hlam, hphi, ht0b, ht45, ht5b, p87_1, u4ehi4]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h6, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h4, h6, h82, hc01, hlam, hphi, ht0b, ht45, ht5b, p87_1, u4ehi4]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p87_1, u4ehi4]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h7, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h82, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h85, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h86, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                              · linarith only [h2, h82, h86, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h82, h85, h9, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                          · linarith only [h0, h119, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h0, h119, h121, h4, h6, h82, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · linarith only [h0, h121, h4, h6, h7, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h0, h124, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                              · linarith only [h1, h126, h130, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h127, h130, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h124, h127, h129, hlam]
                          · linarith only [h0, h128, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                            · linarith only [h127, h135, h136, hc23, hlam, hphi, ht12, u1ehi3]
                            · linarith only [h124, h136, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                          · linarith only [h126, h135, h8, hc14, hlam, hphi, u1ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                          · linarith only [h0, h126, h140, h141, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h141, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                          · linarith only [h126, h144, h8, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h144, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                        · linarith only [h150, h2, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                          · linarith only [h0, h147, h152, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                            · linarith only [h154, h2, h7, hc24, hlam, hphi, ht12, u1ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                              · linarith only [h149, h156, h2, h7, hc13, hlam, hphi, u1ehi3]
                              · rcases h4bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h7, hc45, hlam, hphi, ht12, ht23, ht34, p158_1, u1ehi3]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h7, hc45, hlam, hphi, p158_1, u4ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h7, hc45, hlam, hphi, p158_1, u4ehi3]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h7, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h2, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p158_1, u4ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h2, h7, hc45, hlam, hphi, p158_1, u4ehi3]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h150, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h5, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h148, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h152, hlam, p158_1]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h154, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h6, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h149, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p158_1, u4ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [h156, hlam, p158_0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hc45, hlam, hphi, p158_1, u4ehi0]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p158_1, u1ehi3]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hc45, hlam, hphi, p158_1, u4ehi2]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hc45, hlam, hphi, p158_1, u4ehi3]
                                · have p158_0 := h158c.1
                                  have p158_1 := h158c.2.1
                                  have p158_2 := h158c.2.2.1
                                  have p158_3 := h158c.2.2.2
                                  linarith only [hlam, p158_0]
                      · linarith only [h149, h6, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h148, h5, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h186 | h186
                    · linarith only [h0, h147, h186, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h186, h5, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h189 | h189
                · rcases m.htr 1 2 3 (by decide) (by decide) with h190 | h190
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                      · linarith only [h1, h192, h6, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                          · linarith only [h1, h190, h195, h6, hc12, hlam, hphi, u1ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
                            · linarith only [h0, h191, h197, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h194, h197, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h189, h194, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                      · linarith only [h1, h189, h201, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                          · linarith only [h0, h190, h191, h204, h5, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h207 | h207
                              · rcases h4bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h203, hc04, hlam, hphi, ht0b, ht45, ht5b, p208_1, u4ehi4]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h190, h191, h6, hc34, hlam, hphi, ht12, ht23, p208_1, u1ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h6, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  rcases p208_3 (m.d 0 4) (by simp) with h213 | h213
                                  · rcases p208_3 (m.d 1 4) (by simp) with h214 | h214
                                    · linarith only [h2, h214, hlam]
                                    · linarith only [h203, h214, hlam]
                                  · linarith only [h213, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h2, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h191, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h201, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p208_1, u4ehi4]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h5, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p208_1, u4ehi1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h204, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p208_1, u4ehi4]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h0, h190, h191, h2, h203, h5, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p208_1, u1ehi2, u4ehi4]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h0, h190, h191, h203, h5, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p208_1, u1ehi2, u4ehi4]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h190, h191, hc34, hlam, hphi, ht12, ht23, p208_1, u1ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  rcases p208_3 (m.d 0 4) (by simp) with h232 | h232
                                  · linarith only [h232, h6, hlam]
                                  · linarith only [h189, h232, hlam]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h189, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h203, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h206, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h207, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                              · linarith only [h2, h203, h207, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h191, h203, h206, hlam]
                        · linarith only [h189, h203, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h190, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                      · linarith only [h1, h189, h246, h6, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                        · linarith only [h1, h189, h248, h6, hc14, hlam, hphi, u1ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h250 | h250
                          · linarith only [h1, h244, h250, h6, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h252 | h252
                            · linarith only [h189, h2, h245, h252, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h254 | h254
                              · linarith only [h189, h2, h254, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h1, h254, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h189, h245, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · linarith only [h244, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
              · linarith only [h259, h4, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
                · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                    · linarith only [h0, h263, h5, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                      · linarith only [h1, h259, h265, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
                          · linarith only [h0, h1, h259, h262, h268, h5, hc24, hlam, hphi, ht12, u1ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h270 | h270
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h271 | h271
                              · rcases h4bigk with h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h262, h263, h268, h5, hc23, hc34, hlam, hphi, p272_1]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h5, hlam, p272_1]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h259, hlam, p272_1]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  rcases p272_3 (m.d 0 4) (by simp) with h277 | h277
                                  · rcases p272_3 (m.d 1 4) (by simp) with h278 | h278
                                    · linarith only [h2, h278, hlam]
                                    · linarith only [h267, h278, hlam]
                                  · linarith only [h277, hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h2, hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h263, hlam, p272_1]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h265, hlam, p272_1]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p272_1, u4ehi4]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h2, h268, hc34, hlam, hphi, ht12, ht23, p272_1, u1ehi3]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h268, hc34, hlam, hphi, ht12, ht23, p272_1, u1ehi3]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h268, hlam, p272_1]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  rcases p272_3 (m.d 0 4) (by simp) with h291 | h291
                                  · linarith only [h291, h5, hlam]
                                  · linarith only [h261, h291, hlam]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h2, h267, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p272_1, u4ehi4]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h267, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p272_1, u4ehi4]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h1, h4, h5, hc34, hlam, hphi, ht12, ht23, p272_1, u1ehi2]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  rcases p272_3 (m.d 0 4) (by simp) with h298 | h298
                                  · linarith only [h259, h298, hlam]
                                  · linarith only [h261, h298, hlam]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h261, hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h267, hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h270, hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [h271, hlam, p272_0]
                                · have p272_0 := h272c.1
                                  have p272_1 := h272c.2.1
                                  have p272_2 := h272c.2.2.1
                                  have p272_3 := h272c.2.2.2
                                  linarith only [hlam, p272_0]
                              · linarith only [h2, h267, h271, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h1, h270, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                        · linarith only [h261, h267, h5, hc24, hlam, hphi, ht12, u1ehi3]
                  · linarith only [h262, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h311 | h311
                    · linarith only [h0, h261, h311, h5, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h313 | h313
                      · linarith only [h1, h261, h313, h4, h5, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                        · linarith only [h1, h2, h261, h315, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                          · linarith only [h0, h1, h259, h310, h317, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h319 | h319
                            · linarith only [h0, h261, h310, h317, h319, h5, hc23, hc34, hlam, hphi]
                            · linarith only [h1, h319, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · linarith only [h310, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h323 | h323
            · rcases m.htr 0 3 4 (by decide) (by decide) with h324 | h324
              · rcases m.htr 0 4 5 (by decide) (by decide) with h325 | h325
                · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                  · linarith only [h323, h326, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h331 | h331
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h332 | h332
                            · linarith only [h0, h328, h332, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h2, h330, h331, h332, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h2, h323, h330, h331, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h323, h325, h330, h4, hc23, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h324, h326, h328, h329, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h323, h328, h4, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
                  · linarith only [h323, h339, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h342 | h342
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
                        · linarith only [h2, h325, h343, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h346 | h346
                            · linarith only [h0, h2, h325, h341, h346, h4, hc23, hlam, hphi, ht12, u1ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h348 | h348
                              · linarith only [h0, h2, h325, h341, h345, h348, h4, hc23, hlam, hphi, ht12, u1ehi3]
                              · rcases h4bigk with h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h0, h325, h341, h345, h4, hc23, hc45, hlam, hphi, ht12, p350_1, u1ehi3, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h325, h345, hc45, hlam, hphi, p350_1, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h325, hc45, hlam, hphi, p350_1, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h325, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h2, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h2, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p350_1, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h2, h325, hc45, hlam, hphi, p350_1, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h343, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h323, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h341, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h0, h341, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p350_1, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h346, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h324, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h342, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h345, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h348, hlam, p350_0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hc45, hlam, hphi, p350_1, u4ehi0]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p350_1, u1ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [h345, hc45, hlam, hphi, p350_1, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hc45, hlam, hphi, p350_1, u4ehi3]
                                · have p350_0 := h350c.1
                                  have p350_1 := h350c.2.1
                                  have p350_2 := h350c.2.2.1
                                  have p350_3 := h350c.2.2.2
                                  linarith only [hlam, p350_0]
                          · linarith only [h0, h341, h345, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h324, h325, h339, h341, h342, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h323, h341, h4, hc12, hc23, hlam, hphi]
              · linarith only [h323, h324, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h380 | h380
              · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
                · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
                  · linarith only [h0, h382, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h384 | h384
                    · linarith only [h0, h323, h384, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h386 | h386
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                              · linarith only [h1, h386, h390, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h2, h387, h390, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h1, h323, h386, h387, h389, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h388, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h323, h381, h387, hc24, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h380, h386, h4, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h397 | h397
                  · linarith only [h0, h397, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                    · linarith only [h0, h323, h381, h399, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h402 | h402
                        · linarith only [h0, h323, h381, h402, hc14, hlam, hphi, u1ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                            · linarith only [h0, h323, h381, h405, hc24, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h323, h405, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                          · linarith only [h0, h1, h4, h401, h404, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                      · linarith only [h380, h4, h401, hc23, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
                · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
                  · linarith only [h0, h4, h411, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h413 | h413
                    · linarith only [h0, h323, h4, h410, h413, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h415 | h415
                      · linarith only [h1, h380, h415, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h417 | h417
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                          · linarith only [h0, h380, h4, h418, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h4, h418, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h380, h410, h417, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                  · linarith only [h0, h4, h422, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h424 | h424
                    · linarith only [h0, h380, h4, h410, h424, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
                      · linarith only [h1, h380, h410, h426, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h428 | h428
                        · linarith only [h0, h380, h4, h410, h428, hc14, hlam, hphi, u1ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                          · linarith only [h0, h380, h4, h430, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h4, h430, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h436 | h436
    · linarith only [h0, h436, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h438 | h438
      · linarith only [h0, h438, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
        · linarith only [h0, h440, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h442 | h442
          · rcases m.htr 0 2 4 (by decide) (by decide) with h443 | h443
            · rcases m.htr 0 3 4 (by decide) (by decide) with h444 | h444
              · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
                · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h451 | h451
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h452 | h452
                              · linarith only [h442, h450, h452, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h443, h451, h452, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h455 | h455
                              · linarith only [h450, h451, h455, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                              · rcases h4bigk with h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h438, hlam, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  rcases p457_3 (m.d 0 4) (by simp) with h460 | h460
                                  · rcases p457_3 (m.d 1 4) (by simp) with h461 | h461
                                    · rcases p457_3 (m.d 2 4) (by simp) with h462 | h462
                                      · linarith only [h443, h462, hlam]
                                      · rcases p457_3 (m.d 3 4) (by simp) with h464 | h464
                                        · linarith only [h444, h464, hlam]
                                        · rcases p457_3 (m.d 4 5) (by simp) with h466 | h466
                                          · linarith only [h445, h466, hlam]
                                          · linarith only [h451, h466, hlam]
                                    · linarith only [h447, h461, hlam]
                                  · linarith only [h443, h460, hlam]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  rcases p457_3 (m.d 0 4) (by simp) with h471 | h471
                                  · rcases p457_3 (m.d 1 4) (by simp) with h472 | h472
                                    · rcases p457_3 (m.d 2 4) (by simp) with h473 | h473
                                      · linarith only [h443, h473, hlam]
                                      · linarith only [h450, h473, hlam]
                                    · linarith only [h448, h472, hlam]
                                  · linarith only [h444, h471, hlam]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h436, h444, h446, h450, h451, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p457_1, u4ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h438, h446, h448, hc12, hlam, hphi, p457_1, u1ehi0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  rcases p457_3 (m.d 0 4) (by simp) with h481 | h481
                                  · linarith only [h438, h481, hlam]
                                  · linarith only [h443, h481, hlam]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  rcases p457_3 (m.d 0 4) (by simp) with h484 | h484
                                  · linarith only [h438, h484, hlam]
                                  · linarith only [h444, h484, hlam]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h446, h448, h450, h451, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p457_1, u4ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h443, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h447, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h445, h451, hc04, hlam, hphi, ht0b, ht45, ht5b, p457_1, u4ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h451, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h444, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h448, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h450, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h455, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h445, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h449, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h445, hc04, hlam, hphi, ht0b, ht45, ht5b, p457_1, u4ehi2]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h438, h445, h446, h448, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p457_1, u4ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h503 | h503
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
                              · rcases h4bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h438, hlam, p505_1]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h438, h446, h448, h503, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p505_1, u4ehi4]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h438, h446, h448, h450, h503, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p505_1, u4ehi4]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  rcases p505_3 (m.d 0 4) (by simp) with h510 | h510
                                  · rcases p505_3 (m.d 1 4) (by simp) with h511 | h511
                                    · rcases p505_3 (m.d 2 4) (by simp) with h512 | h512
                                      · linarith only [h443, h512, hlam]
                                      · linarith only [h503, h512, hlam]
                                    · linarith only [h449, h511, hlam]
                                  · linarith only [h510, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h438, h446, h448, hc12, hlam, hphi, p505_1, u1ehi0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h446, h448, h503, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p505_1, u4ehi4]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h446, h448, h450, h503, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p505_1, u4ehi4]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  rcases p505_3 (m.d 0 4) (by simp) with h521 | h521
                                  · linarith only [h438, h521, hlam]
                                  · linarith only [h445, h521, hlam]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h443, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h447, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h450, hlam, p505_1]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h0, h443, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p505_1, u4ehi4]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h444, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h448, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h436, h444, h446, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p505_1, u4ehi2]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h436, h444, h446, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p505_1, u4ehi4]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h445, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h449, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h503, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [h504, hlam, p505_0]
                                · have p505_0 := h505c.1
                                  have p505_1 := h505c.2.1
                                  have p505_2 := h505c.2.2.1
                                  have p505_3 := h505c.2.2.2
                                  linarith only [hlam, p505_0]
                              · linarith only [h0, h443, h503, h504, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h540 | h540
                              · linarith only [h436, h444, h446, h503, h540, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                              · rcases h4bigk with h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h438, hlam, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  rcases p542_3 (m.d 0 4) (by simp) with h545 | h545
                                  · rcases p542_3 (m.d 1 4) (by simp) with h546 | h546
                                    · rcases p542_3 (m.d 2 4) (by simp) with h547 | h547
                                      · linarith only [h443, h547, hlam]
                                      · rcases p542_3 (m.d 3 4) (by simp) with h549 | h549
                                        · linarith only [h444, h549, hlam]
                                        · linarith only [h450, h549, hlam]
                                    · linarith only [h447, h546, hlam]
                                  · linarith only [h443, h545, hlam]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  rcases p542_3 (m.d 0 4) (by simp) with h554 | h554
                                  · rcases p542_3 (m.d 1 4) (by simp) with h555 | h555
                                    · rcases p542_3 (m.d 2 4) (by simp) with h556 | h556
                                      · linarith only [h443, h556, hlam]
                                      · rcases p542_3 (m.d 3 4) (by simp) with h558 | h558
                                        · linarith only [h444, h558, hlam]
                                        · rcases p542_3 (m.d 4 5) (by simp) with h560 | h560
                                          · linarith only [h445, h560, hlam]
                                          · linarith only [h540, h560, hlam]
                                    · linarith only [h448, h555, hlam]
                                  · linarith only [h444, h554, hlam]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h438, h446, h448, h450, h540, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h438, h446, h448, hc12, hlam, hphi, p542_1, u1ehi0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  rcases p542_3 (m.d 0 4) (by simp) with h568 | h568
                                  · linarith only [h438, h568, hlam]
                                  · linarith only [h443, h568, hlam]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  rcases p542_3 (m.d 0 4) (by simp) with h571 | h571
                                  · linarith only [h438, h571, hlam]
                                  · linarith only [h444, h571, hlam]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h446, h448, h450, h540, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h443, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h447, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h450, hlam, p542_1]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h503, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h444, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h448, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h445, h540, hc04, hlam, hphi, ht0b, ht45, ht5b, p542_1, u4ehi2]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h540, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h445, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h449, hlam, p542_0]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h438, h445, h446, h448, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p542_1, u4ehi2]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [h438, h445, h446, h448, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p542_1, u4ehi3]
                                · have p542_0 := h542c.1
                                  have p542_1 := h542c.2.1
                                  have p542_2 := h542c.2.2.1
                                  have p542_3 := h542c.2.2.2
                                  linarith only [hlam, p542_0]
                        · linarith only [h438, h445, h449, hlam]
                      · linarith only [h436, h448, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h447, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h446, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h594 | h594
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h595 | h595
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                        · linarith only [h438, h445, h594, h596, h597, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h438, h597, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                      · linarith only [h436, h596, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h443, h595, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · linarith only [h0, h442, h594, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h603 | h603
                · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h606 | h606
                      · linarith only [h436, h444, h604, h606, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h436, h606, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h605, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h442, h604, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h611 | h611
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h612 | h612
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h613 | h613
                      · linarith only [h436, h444, h613, hc13, hlam, hphi, u1ehi0]
                      · linarith only [h436, h613, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h443, h603, h612, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · linarith only [h0, h442, h611, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h618 | h618
              · linarith only [h442, h443, h618, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
                    · linarith only [h0, h443, h622, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h622, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h621, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h627 | h627
                    · linarith only [h436, h442, h443, h627, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h627, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h442, h443, h620, h626, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h631 | h631
            · rcases m.htr 0 3 4 (by decide) (by decide) with h632 | h632
              · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
                · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                  · linarith only [h442, h631, h634, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h634, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
                  · linarith only [h0, h442, h637, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h637, hc23, hlam, hphi, ht12, u1ehi0]
              · linarith only [h442, h631, h632, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h641 | h641
              · rcases m.htr 0 4 5 (by decide) (by decide) with h642 | h642
                · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                  · linarith only [h0, h442, h643, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h643, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                  · linarith only [h0, h442, h646, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h646, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
                  · linarith only [h0, h442, h650, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h650, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
                  · linarith only [h0, h442, h653, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h653, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAB1_M_IR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have h1emax := hb1.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h1emax with h0 | h0 | h0 | h0 | h0
  · rcases h4bigk with h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h3 | h3
      · rcases p1_3 (m.d 1 4) (by simp) with h4 | h4
        · linarith only [h4, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h6 | h6
          · rcases p1_3 (m.d 3 4) (by simp) with h7 | h7
            · rcases p1_3 (m.d 4 5) (by simp) with h8 | h8
              · linarith only [h8, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h11 | h11
              · linarith only [h11, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h11, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
          · rcases p1_3 (m.d 3 4) (by simp) with h14 | h14
            · rcases p1_3 (m.d 4 5) (by simp) with h15 | h15
              · linarith only [h15, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h15, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h18 | h18
              · linarith only [h18, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h18, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
      · linarith only [h3, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h22 | h22
      · rcases p1_3 (m.d 1 4) (by simp) with h23 | h23
        · rcases p1_3 (m.d 2 4) (by simp) with h24 | h24
          · linarith only [h24, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h26 | h26
            · rcases p1_3 (m.d 4 5) (by simp) with h27 | h27
              · linarith only [h27, hc45, hlam, hphi, p1_1, u4ehi2]
              · linarith only [h27, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h30 | h30
              · linarith only [h30, hc45, hlam, hphi, p1_1, u4ehi2]
              · linarith only [h30, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
        · rcases p1_3 (m.d 2 4) (by simp) with h33 | h33
          · linarith only [h33, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h35 | h35
            · rcases p1_3 (m.d 4 5) (by simp) with h36 | h36
              · linarith only [h23, h36, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h36, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h39 | h39
              · linarith only [h23, h39, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h39, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
      · linarith only [h22, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h43 | h43
      · rcases p1_3 (m.d 1 4) (by simp) with h44 | h44
        · rcases p1_3 (m.d 2 4) (by simp) with h45 | h45
          · rcases p1_3 (m.d 3 4) (by simp) with h46 | h46
            · linarith only [h46, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h48 | h48
              · linarith only [h48, hc45, hlam, hphi, p1_1, u4ehi3]
              · linarith only [h48, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
          · rcases p1_3 (m.d 3 4) (by simp) with h51 | h51
            · linarith only [h51, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h53 | h53
              · linarith only [h45, h53, hc45, hlam, hphi, p1_1, u4ehi2]
              · linarith only [h53, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
        · rcases p1_3 (m.d 2 4) (by simp) with h56 | h56
          · rcases p1_3 (m.d 3 4) (by simp) with h57 | h57
            · linarith only [h57, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h59 | h59
              · linarith only [h44, h59, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h59, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
          · rcases p1_3 (m.d 3 4) (by simp) with h62 | h62
            · linarith only [h62, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h64 | h64
              · linarith only [h44, h64, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h64, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
      · linarith only [h43, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h69 | h69
      · linarith only [h69, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h71 | h71
        · rcases p1_3 (m.d 2 4) (by simp) with h72 | h72
          · rcases p1_3 (m.d 3 4) (by simp) with h73 | h73
            · rcases p1_3 (m.d 4 5) (by simp) with h74 | h74
              · linarith only [h74, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h74, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h77 | h77
              · linarith only [h77, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h77, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
          · rcases p1_3 (m.d 3 4) (by simp) with h80 | h80
            · rcases p1_3 (m.d 4 5) (by simp) with h81 | h81
              · linarith only [h81, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h81, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h84 | h84
              · linarith only [h84, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h84, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
        · linarith only [h71, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h89 | h89
      · rcases p1_3 (m.d 1 4) (by simp) with h90 | h90
        · rcases p1_3 (m.d 2 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h93 | h93
            · rcases p1_3 (m.d 4 5) (by simp) with h94 | h94
              · linarith only [h94, hc45, hlam, hphi, p1_1, u4ehi2]
              · linarith only [h89, h94, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h97 | h97
              · linarith only [h97, hc45, hlam, hphi, p1_1, u4ehi2]
              · linarith only [h97, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
        · linarith only [h90, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h101 | h101
        · rcases p1_3 (m.d 2 4) (by simp) with h102 | h102
          · linarith only [h102, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h104 | h104
            · rcases p1_3 (m.d 4 5) (by simp) with h105 | h105
              · linarith only [h105, h89, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h105, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h108 | h108
              · linarith only [h108, h89, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h108, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
        · linarith only [h101, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h112 | h112
      · rcases p1_3 (m.d 1 4) (by simp) with h113 | h113
        · rcases p1_3 (m.d 2 4) (by simp) with h114 | h114
          · rcases p1_3 (m.d 3 4) (by simp) with h115 | h115
            · linarith only [h115, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h117 | h117
              · linarith only [h117, hc45, hlam, hphi, p1_1, u4ehi3]
              · linarith only [h112, h117, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
          · rcases p1_3 (m.d 3 4) (by simp) with h120 | h120
            · linarith only [h120, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h122 | h122
              · linarith only [h114, h122, hc45, hlam, hphi, p1_1, u4ehi2]
              · linarith only [h122, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
        · linarith only [h113, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h126 | h126
        · rcases p1_3 (m.d 2 4) (by simp) with h127 | h127
          · rcases p1_3 (m.d 3 4) (by simp) with h128 | h128
            · linarith only [h128, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h130 | h130
              · linarith only [h112, h130, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h130, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
          · rcases p1_3 (m.d 3 4) (by simp) with h133 | h133
            · linarith only [h133, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h135 | h135
              · linarith only [h112, h135, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h135, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
        · linarith only [h126, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h140 | h140
      · linarith only [h140, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h142 | h142
        · rcases p1_3 (m.d 2 4) (by simp) with h143 | h143
          · rcases p1_3 (m.d 3 4) (by simp) with h144 | h144
            · rcases p1_3 (m.d 4 5) (by simp) with h145 | h145
              · linarith only [h145, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h145, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h148 | h148
              · linarith only [h148, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h148, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
          · linarith only [h143, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h152 | h152
          · rcases p1_3 (m.d 3 4) (by simp) with h153 | h153
            · rcases p1_3 (m.d 4 5) (by simp) with h154 | h154
              · linarith only [h154, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h154, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h157 | h157
              · linarith only [h157, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h157, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
          · linarith only [h152, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h161 | h161
      · rcases p1_3 (m.d 1 4) (by simp) with h162 | h162
        · linarith only [h162, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h164 | h164
          · rcases p1_3 (m.d 3 4) (by simp) with h165 | h165
            · rcases p1_3 (m.d 4 5) (by simp) with h166 | h166
              · linarith only [h166, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h161, h166, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h169 | h169
              · linarith only [h169, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h169, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
          · linarith only [h164, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h173 | h173
        · linarith only [h173, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h175 | h175
          · rcases p1_3 (m.d 3 4) (by simp) with h176 | h176
            · rcases p1_3 (m.d 4 5) (by simp) with h177 | h177
              · linarith only [h161, h177, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h177, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
            · rcases p1_3 (m.d 4 5) (by simp) with h180 | h180
              · linarith only [h161, h180, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h180, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
          · linarith only [h175, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h185 | h185
      · rcases p1_3 (m.d 1 4) (by simp) with h186 | h186
        · rcases p1_3 (m.d 2 4) (by simp) with h187 | h187
          · rcases p1_3 (m.d 3 4) (by simp) with h188 | h188
            · linarith only [h188, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h190 | h190
              · linarith only [h190, hc45, hlam, hphi, p1_1, u4ehi3]
              · linarith only [h185, h190, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
          · linarith only [h187, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h194 | h194
          · rcases p1_3 (m.d 3 4) (by simp) with h195 | h195
            · linarith only [h195, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h197 | h197
              · linarith only [h186, h197, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h197, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
          · linarith only [h194, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h201 | h201
        · rcases p1_3 (m.d 2 4) (by simp) with h202 | h202
          · rcases p1_3 (m.d 3 4) (by simp) with h203 | h203
            · linarith only [h203, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h205 | h205
              · linarith only [h185, h205, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h201, h205, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
          · linarith only [h202, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h209 | h209
          · rcases p1_3 (m.d 3 4) (by simp) with h210 | h210
            · linarith only [h210, hlam, p1_0]
            · rcases p1_3 (m.d 4 5) (by simp) with h212 | h212
              · linarith only [h185, h212, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h212, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
          · linarith only [h209, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h217 | h217
      · linarith only [h217, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h219 | h219
        · rcases p1_3 (m.d 2 4) (by simp) with h220 | h220
          · rcases p1_3 (m.d 3 4) (by simp) with h221 | h221
            · rcases p1_3 (m.d 4 5) (by simp) with h222 | h222
              · linarith only [h222, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h219, h222, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
            · linarith only [h221, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h226 | h226
            · rcases p1_3 (m.d 4 5) (by simp) with h227 | h227
              · linarith only [h227, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h219, h227, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
            · linarith only [h226, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h231 | h231
          · rcases p1_3 (m.d 3 4) (by simp) with h232 | h232
            · rcases p1_3 (m.d 4 5) (by simp) with h233 | h233
              · linarith only [h233, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h231, h233, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
            · linarith only [h232, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h237 | h237
            · rcases p1_3 (m.d 4 5) (by simp) with h238 | h238
              · linarith only [h238, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h238, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1_1, u5ehi4]
            · linarith only [h237, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h242 | h242
      · rcases p1_3 (m.d 1 4) (by simp) with h243 | h243
        · linarith only [h243, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h245 | h245
          · rcases p1_3 (m.d 3 4) (by simp) with h246 | h246
            · rcases p1_3 (m.d 4 5) (by simp) with h247 | h247
              · linarith only [h247, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h242, h247, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · linarith only [h246, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h251 | h251
            · rcases p1_3 (m.d 4 5) (by simp) with h252 | h252
              · linarith only [h252, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1_1, u5ehi4]
            · linarith only [h251, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h256 | h256
        · linarith only [h256, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h258 | h258
          · rcases p1_3 (m.d 3 4) (by simp) with h259 | h259
            · rcases p1_3 (m.d 4 5) (by simp) with h260 | h260
              · linarith only [h242, h260, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h258, h260, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1_1, u5ehi4]
            · linarith only [h259, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h264 | h264
            · rcases p1_3 (m.d 4 5) (by simp) with h265 | h265
              · linarith only [h242, h265, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h265, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1_1, u5ehi4]
            · linarith only [h264, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      rcases p1_3 (m.d 0 4) (by simp) with h269 | h269
      · rcases p1_3 (m.d 1 4) (by simp) with h270 | h270
        · rcases p1_3 (m.d 2 4) (by simp) with h271 | h271
          · linarith only [h271, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h273 | h273
            · rcases p1_3 (m.d 4 5) (by simp) with h274 | h274
              · linarith only [h274, hc45, hlam, hphi, p1_1, u4ehi2]
              · linarith only [h269, h274, hc04, hlam, hphi, ht0b, ht5b, p1_1, u5ehi4]
            · linarith only [h273, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h278 | h278
          · linarith only [h278, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h280 | h280
            · rcases p1_3 (m.d 4 5) (by simp) with h281 | h281
              · linarith only [h270, h281, hc45, hlam, hphi, p1_1, u4ehi1]
              · linarith only [h281, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1_1, u5ehi4]
            · linarith only [h280, hlam, p1_0]
      · rcases p1_3 (m.d 1 4) (by simp) with h285 | h285
        · rcases p1_3 (m.d 2 4) (by simp) with h286 | h286
          · linarith only [h286, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h288 | h288
            · rcases p1_3 (m.d 4 5) (by simp) with h289 | h289
              · linarith only [h269, h289, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h285, h289, hc14, hlam, hphi, ht01, ht0b, ht5b, p1_1, u5ehi4]
            · linarith only [h288, hlam, p1_0]
        · rcases p1_3 (m.d 2 4) (by simp) with h293 | h293
          · linarith only [h293, hlam, p1_0]
          · rcases p1_3 (m.d 3 4) (by simp) with h295 | h295
            · rcases p1_3 (m.d 4 5) (by simp) with h296 | h296
              · linarith only [h269, h296, hc45, hlam, hphi, p1_1, u4ehi0]
              · linarith only [h296, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1_1, u5ehi4]
            · linarith only [h295, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1_1, u5ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u4ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u4ehi1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u4ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u4ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
  · rcases h4bigk with h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h309 | h309
      · rcases p307_3 (m.d 1 4) (by simp) with h310 | h310
        · linarith only [h310, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h312 | h312
          · rcases p307_3 (m.d 3 4) (by simp) with h313 | h313
            · rcases p307_3 (m.d 4 5) (by simp) with h314 | h314
              · linarith only [h314, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h314, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h317 | h317
              · linarith only [h317, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h317, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
          · rcases p307_3 (m.d 3 4) (by simp) with h320 | h320
            · rcases p307_3 (m.d 4 5) (by simp) with h321 | h321
              · linarith only [h321, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h321, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h324 | h324
              · linarith only [h324, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h324, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
      · linarith only [h309, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h328 | h328
      · rcases p307_3 (m.d 1 4) (by simp) with h329 | h329
        · rcases p307_3 (m.d 2 4) (by simp) with h330 | h330
          · linarith only [h330, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h332 | h332
            · rcases p307_3 (m.d 4 5) (by simp) with h333 | h333
              · linarith only [h333, hc45, hlam, hphi, p307_1, u4ehi2]
              · linarith only [h333, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h336 | h336
              · linarith only [h336, hc45, hlam, hphi, p307_1, u4ehi2]
              · linarith only [h336, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
        · rcases p307_3 (m.d 2 4) (by simp) with h339 | h339
          · linarith only [h339, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h341 | h341
            · rcases p307_3 (m.d 4 5) (by simp) with h342 | h342
              · linarith only [h329, h342, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h342, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h345 | h345
              · linarith only [h329, h345, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h345, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
      · linarith only [h328, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h349 | h349
      · rcases p307_3 (m.d 1 4) (by simp) with h350 | h350
        · rcases p307_3 (m.d 2 4) (by simp) with h351 | h351
          · rcases p307_3 (m.d 3 4) (by simp) with h352 | h352
            · linarith only [h352, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h354 | h354
              · linarith only [h354, hc45, hlam, hphi, p307_1, u4ehi3]
              · linarith only [h354, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
          · rcases p307_3 (m.d 3 4) (by simp) with h357 | h357
            · linarith only [h357, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h359 | h359
              · linarith only [h351, h359, hc45, hlam, hphi, p307_1, u4ehi2]
              · linarith only [h359, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
        · rcases p307_3 (m.d 2 4) (by simp) with h362 | h362
          · rcases p307_3 (m.d 3 4) (by simp) with h363 | h363
            · linarith only [h363, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h365 | h365
              · linarith only [h350, h365, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h365, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
          · rcases p307_3 (m.d 3 4) (by simp) with h368 | h368
            · linarith only [h368, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h370 | h370
              · linarith only [h350, h370, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h370, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
      · linarith only [h349, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h375 | h375
      · linarith only [h375, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h377 | h377
        · rcases p307_3 (m.d 2 4) (by simp) with h378 | h378
          · rcases p307_3 (m.d 3 4) (by simp) with h379 | h379
            · rcases p307_3 (m.d 4 5) (by simp) with h380 | h380
              · linarith only [h380, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h380, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h383 | h383
              · linarith only [h383, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h383, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
          · rcases p307_3 (m.d 3 4) (by simp) with h386 | h386
            · rcases p307_3 (m.d 4 5) (by simp) with h387 | h387
              · linarith only [h387, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h387, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h390 | h390
              · linarith only [h390, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h390, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
        · linarith only [h377, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h395 | h395
      · rcases p307_3 (m.d 1 4) (by simp) with h396 | h396
        · rcases p307_3 (m.d 2 4) (by simp) with h397 | h397
          · linarith only [h397, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h399 | h399
            · rcases p307_3 (m.d 4 5) (by simp) with h400 | h400
              · linarith only [h400, hc45, hlam, hphi, p307_1, u4ehi2]
              · linarith only [h395, h400, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h403 | h403
              · linarith only [h403, hc45, hlam, hphi, p307_1, u4ehi2]
              · linarith only [h403, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
        · linarith only [h396, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h407 | h407
        · rcases p307_3 (m.d 2 4) (by simp) with h408 | h408
          · linarith only [h408, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h410 | h410
            · rcases p307_3 (m.d 4 5) (by simp) with h411 | h411
              · linarith only [h395, h411, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h411, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h414 | h414
              · linarith only [h395, h414, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h414, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
        · linarith only [h407, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h418 | h418
      · rcases p307_3 (m.d 1 4) (by simp) with h419 | h419
        · rcases p307_3 (m.d 2 4) (by simp) with h420 | h420
          · rcases p307_3 (m.d 3 4) (by simp) with h421 | h421
            · linarith only [h421, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h423 | h423
              · linarith only [h423, hc45, hlam, hphi, p307_1, u4ehi3]
              · linarith only [h418, h423, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
          · rcases p307_3 (m.d 3 4) (by simp) with h426 | h426
            · linarith only [h426, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h428 | h428
              · linarith only [h420, h428, hc45, hlam, hphi, p307_1, u4ehi2]
              · linarith only [h428, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
        · linarith only [h419, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h432 | h432
        · rcases p307_3 (m.d 2 4) (by simp) with h433 | h433
          · rcases p307_3 (m.d 3 4) (by simp) with h434 | h434
            · linarith only [h434, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h436 | h436
              · linarith only [h418, h436, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h436, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
          · rcases p307_3 (m.d 3 4) (by simp) with h439 | h439
            · linarith only [h439, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h441 | h441
              · linarith only [h418, h441, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h441, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
        · linarith only [h432, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h446 | h446
      · linarith only [h446, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h448 | h448
        · rcases p307_3 (m.d 2 4) (by simp) with h449 | h449
          · rcases p307_3 (m.d 3 4) (by simp) with h450 | h450
            · rcases p307_3 (m.d 4 5) (by simp) with h451 | h451
              · linarith only [h451, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h451, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h454 | h454
              · linarith only [h454, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h454, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
          · linarith only [h449, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h458 | h458
          · rcases p307_3 (m.d 3 4) (by simp) with h459 | h459
            · rcases p307_3 (m.d 4 5) (by simp) with h460 | h460
              · linarith only [h460, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h460, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h463 | h463
              · linarith only [h463, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h463, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
          · linarith only [h458, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h467 | h467
      · rcases p307_3 (m.d 1 4) (by simp) with h468 | h468
        · linarith only [h468, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h470 | h470
          · rcases p307_3 (m.d 3 4) (by simp) with h471 | h471
            · rcases p307_3 (m.d 4 5) (by simp) with h472 | h472
              · linarith only [h472, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h467, h472, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h475 | h475
              · linarith only [h475, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h475, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
          · linarith only [h470, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h479 | h479
        · linarith only [h479, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h481 | h481
          · rcases p307_3 (m.d 3 4) (by simp) with h482 | h482
            · rcases p307_3 (m.d 4 5) (by simp) with h483 | h483
              · linarith only [h467, h483, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h483, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
            · rcases p307_3 (m.d 4 5) (by simp) with h486 | h486
              · linarith only [h467, h486, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h486, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
          · linarith only [h481, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h491 | h491
      · rcases p307_3 (m.d 1 4) (by simp) with h492 | h492
        · rcases p307_3 (m.d 2 4) (by simp) with h493 | h493
          · rcases p307_3 (m.d 3 4) (by simp) with h494 | h494
            · linarith only [h494, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h496 | h496
              · linarith only [h496, hc45, hlam, hphi, p307_1, u4ehi3]
              · linarith only [h491, h496, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
          · linarith only [h493, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h500 | h500
          · rcases p307_3 (m.d 3 4) (by simp) with h501 | h501
            · linarith only [h501, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h503 | h503
              · linarith only [h492, h503, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h503, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
          · linarith only [h500, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h507 | h507
        · rcases p307_3 (m.d 2 4) (by simp) with h508 | h508
          · rcases p307_3 (m.d 3 4) (by simp) with h509 | h509
            · linarith only [h509, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h511 | h511
              · linarith only [h491, h511, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h507, h511, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
          · linarith only [h508, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h515 | h515
          · rcases p307_3 (m.d 3 4) (by simp) with h516 | h516
            · linarith only [h516, hlam, p307_0]
            · rcases p307_3 (m.d 4 5) (by simp) with h518 | h518
              · linarith only [h491, h518, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h518, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
          · linarith only [h515, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h523 | h523
      · linarith only [h523, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h525 | h525
        · rcases p307_3 (m.d 2 4) (by simp) with h526 | h526
          · rcases p307_3 (m.d 3 4) (by simp) with h527 | h527
            · rcases p307_3 (m.d 4 5) (by simp) with h528 | h528
              · linarith only [h528, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h525, h528, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
            · linarith only [h527, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h532 | h532
            · rcases p307_3 (m.d 4 5) (by simp) with h533 | h533
              · linarith only [h533, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h533, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi4]
            · linarith only [h532, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h537 | h537
          · rcases p307_3 (m.d 3 4) (by simp) with h538 | h538
            · rcases p307_3 (m.d 4 5) (by simp) with h539 | h539
              · linarith only [h539, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h537, h539, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
            · linarith only [h538, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h543 | h543
            · rcases p307_3 (m.d 4 5) (by simp) with h544 | h544
              · linarith only [h544, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h544, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi4]
            · linarith only [h543, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h548 | h548
      · rcases p307_3 (m.d 1 4) (by simp) with h549 | h549
        · linarith only [h549, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h551 | h551
          · rcases p307_3 (m.d 3 4) (by simp) with h552 | h552
            · rcases p307_3 (m.d 4 5) (by simp) with h553 | h553
              · linarith only [h553, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h548, h553, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · linarith only [h552, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h557 | h557
            · rcases p307_3 (m.d 4 5) (by simp) with h558 | h558
              · linarith only [h558, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h558, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi4]
            · linarith only [h557, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h562 | h562
        · linarith only [h562, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h564 | h564
          · rcases p307_3 (m.d 3 4) (by simp) with h565 | h565
            · rcases p307_3 (m.d 4 5) (by simp) with h566 | h566
              · linarith only [h548, h566, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h564, h566, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p307_1, u5ehi4]
            · linarith only [h565, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h570 | h570
            · rcases p307_3 (m.d 4 5) (by simp) with h571 | h571
              · linarith only [h548, h571, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h571, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi4]
            · linarith only [h570, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      rcases p307_3 (m.d 0 4) (by simp) with h575 | h575
      · rcases p307_3 (m.d 1 4) (by simp) with h576 | h576
        · rcases p307_3 (m.d 2 4) (by simp) with h577 | h577
          · linarith only [h577, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h579 | h579
            · rcases p307_3 (m.d 4 5) (by simp) with h580 | h580
              · linarith only [h580, hc45, hlam, hphi, p307_1, u4ehi2]
              · linarith only [h575, h580, hc04, hlam, hphi, ht0b, ht5b, p307_1, u5ehi4]
            · linarith only [h579, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h584 | h584
          · linarith only [h584, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h586 | h586
            · rcases p307_3 (m.d 4 5) (by simp) with h587 | h587
              · linarith only [h576, h587, hc45, hlam, hphi, p307_1, u4ehi1]
              · linarith only [h587, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi4]
            · linarith only [h586, hlam, p307_0]
      · rcases p307_3 (m.d 1 4) (by simp) with h591 | h591
        · rcases p307_3 (m.d 2 4) (by simp) with h592 | h592
          · linarith only [h592, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h594 | h594
            · rcases p307_3 (m.d 4 5) (by simp) with h595 | h595
              · linarith only [h575, h595, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h591, h595, hc14, hlam, hphi, ht01, ht0b, ht5b, p307_1, u5ehi4]
            · linarith only [h594, hlam, p307_0]
        · rcases p307_3 (m.d 2 4) (by simp) with h599 | h599
          · linarith only [h599, hlam, p307_0]
          · rcases p307_3 (m.d 3 4) (by simp) with h601 | h601
            · rcases p307_3 (m.d 4 5) (by simp) with h602 | h602
              · linarith only [h575, h602, hc45, hlam, hphi, p307_1, u4ehi0]
              · linarith only [h602, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi4]
            · linarith only [h601, hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hlam, p307_0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi4]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc45, hlam, hphi, p307_1, u4ehi0]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc45, hlam, hphi, p307_1, u4ehi1]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc45, hlam, hphi, p307_1, u4ehi2]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hc45, hlam, hphi, p307_1, u4ehi3]
    · have p307_0 := h307c.1
      have p307_1 := h307c.2.1
      have p307_2 := h307c.2.2.1
      have p307_3 := h307c.2.2.2
      linarith only [hlam, p307_0]
  · rcases h4bigk with h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h615 | h615
      · rcases p613_3 (m.d 1 4) (by simp) with h616 | h616
        · linarith only [h616, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h618 | h618
          · rcases p613_3 (m.d 3 4) (by simp) with h619 | h619
            · rcases p613_3 (m.d 4 5) (by simp) with h620 | h620
              · linarith only [h620, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h620, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h623 | h623
              · linarith only [h623, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h623, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
          · rcases p613_3 (m.d 3 4) (by simp) with h626 | h626
            · rcases p613_3 (m.d 4 5) (by simp) with h627 | h627
              · linarith only [h627, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h627, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h630 | h630
              · linarith only [h630, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h630, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
      · linarith only [h615, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h634 | h634
      · rcases p613_3 (m.d 1 4) (by simp) with h635 | h635
        · rcases p613_3 (m.d 2 4) (by simp) with h636 | h636
          · linarith only [h636, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h638 | h638
            · rcases p613_3 (m.d 4 5) (by simp) with h639 | h639
              · linarith only [h639, hc45, hlam, hphi, p613_1, u4ehi2]
              · linarith only [h639, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h642 | h642
              · linarith only [h642, hc45, hlam, hphi, p613_1, u4ehi2]
              · linarith only [h642, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
        · rcases p613_3 (m.d 2 4) (by simp) with h645 | h645
          · linarith only [h645, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h647 | h647
            · rcases p613_3 (m.d 4 5) (by simp) with h648 | h648
              · linarith only [h635, h648, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h648, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h651 | h651
              · linarith only [h635, h651, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h651, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
      · linarith only [h634, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h655 | h655
      · rcases p613_3 (m.d 1 4) (by simp) with h656 | h656
        · rcases p613_3 (m.d 2 4) (by simp) with h657 | h657
          · rcases p613_3 (m.d 3 4) (by simp) with h658 | h658
            · linarith only [h658, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h660 | h660
              · linarith only [h660, hc45, hlam, hphi, p613_1, u4ehi3]
              · linarith only [h660, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
          · rcases p613_3 (m.d 3 4) (by simp) with h663 | h663
            · linarith only [h663, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h665 | h665
              · linarith only [h657, h665, hc45, hlam, hphi, p613_1, u4ehi2]
              · linarith only [h665, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
        · rcases p613_3 (m.d 2 4) (by simp) with h668 | h668
          · rcases p613_3 (m.d 3 4) (by simp) with h669 | h669
            · linarith only [h669, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h671 | h671
              · linarith only [h656, h671, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h671, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
          · rcases p613_3 (m.d 3 4) (by simp) with h674 | h674
            · linarith only [h674, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h676 | h676
              · linarith only [h656, h676, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h676, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
      · linarith only [h655, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h681 | h681
      · linarith only [h681, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h683 | h683
        · rcases p613_3 (m.d 2 4) (by simp) with h684 | h684
          · rcases p613_3 (m.d 3 4) (by simp) with h685 | h685
            · rcases p613_3 (m.d 4 5) (by simp) with h686 | h686
              · linarith only [h686, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h686, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h689 | h689
              · linarith only [h689, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h689, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
          · rcases p613_3 (m.d 3 4) (by simp) with h692 | h692
            · rcases p613_3 (m.d 4 5) (by simp) with h693 | h693
              · linarith only [h693, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h693, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h696 | h696
              · linarith only [h696, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h696, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
        · linarith only [h683, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h701 | h701
      · rcases p613_3 (m.d 1 4) (by simp) with h702 | h702
        · rcases p613_3 (m.d 2 4) (by simp) with h703 | h703
          · linarith only [h703, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h705 | h705
            · rcases p613_3 (m.d 4 5) (by simp) with h706 | h706
              · linarith only [h706, hc45, hlam, hphi, p613_1, u4ehi2]
              · linarith only [h701, h706, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h709 | h709
              · linarith only [h709, hc45, hlam, hphi, p613_1, u4ehi2]
              · linarith only [h709, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
        · linarith only [h702, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h713 | h713
        · rcases p613_3 (m.d 2 4) (by simp) with h714 | h714
          · linarith only [h714, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h716 | h716
            · rcases p613_3 (m.d 4 5) (by simp) with h717 | h717
              · linarith only [h701, h717, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h717, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h720 | h720
              · linarith only [h701, h720, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h720, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
        · linarith only [h713, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h724 | h724
      · rcases p613_3 (m.d 1 4) (by simp) with h725 | h725
        · rcases p613_3 (m.d 2 4) (by simp) with h726 | h726
          · rcases p613_3 (m.d 3 4) (by simp) with h727 | h727
            · linarith only [h727, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h729 | h729
              · linarith only [h729, hc45, hlam, hphi, p613_1, u4ehi3]
              · linarith only [h724, h729, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
          · rcases p613_3 (m.d 3 4) (by simp) with h732 | h732
            · linarith only [h732, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h734 | h734
              · linarith only [h726, h734, hc45, hlam, hphi, p613_1, u4ehi2]
              · linarith only [h734, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
        · linarith only [h725, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h738 | h738
        · rcases p613_3 (m.d 2 4) (by simp) with h739 | h739
          · rcases p613_3 (m.d 3 4) (by simp) with h740 | h740
            · linarith only [h740, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h742 | h742
              · linarith only [h724, h742, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h742, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
          · rcases p613_3 (m.d 3 4) (by simp) with h745 | h745
            · linarith only [h745, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h747 | h747
              · linarith only [h724, h747, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h747, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
        · linarith only [h738, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h752 | h752
      · linarith only [h752, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h754 | h754
        · rcases p613_3 (m.d 2 4) (by simp) with h755 | h755
          · rcases p613_3 (m.d 3 4) (by simp) with h756 | h756
            · rcases p613_3 (m.d 4 5) (by simp) with h757 | h757
              · linarith only [h757, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h757, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h760 | h760
              · linarith only [h760, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h760, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
          · linarith only [h755, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h764 | h764
          · rcases p613_3 (m.d 3 4) (by simp) with h765 | h765
            · rcases p613_3 (m.d 4 5) (by simp) with h766 | h766
              · linarith only [h766, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h766, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h769 | h769
              · linarith only [h769, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h769, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
          · linarith only [h764, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h773 | h773
      · rcases p613_3 (m.d 1 4) (by simp) with h774 | h774
        · linarith only [h774, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h776 | h776
          · rcases p613_3 (m.d 3 4) (by simp) with h777 | h777
            · rcases p613_3 (m.d 4 5) (by simp) with h778 | h778
              · linarith only [h778, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h773, h778, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h781 | h781
              · linarith only [h781, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h781, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
          · linarith only [h776, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h785 | h785
        · linarith only [h785, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h787 | h787
          · rcases p613_3 (m.d 3 4) (by simp) with h788 | h788
            · rcases p613_3 (m.d 4 5) (by simp) with h789 | h789
              · linarith only [h773, h789, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h789, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
            · rcases p613_3 (m.d 4 5) (by simp) with h792 | h792
              · linarith only [h773, h792, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h792, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
          · linarith only [h787, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h797 | h797
      · rcases p613_3 (m.d 1 4) (by simp) with h798 | h798
        · rcases p613_3 (m.d 2 4) (by simp) with h799 | h799
          · rcases p613_3 (m.d 3 4) (by simp) with h800 | h800
            · linarith only [h800, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h802 | h802
              · linarith only [h802, hc45, hlam, hphi, p613_1, u4ehi3]
              · linarith only [h797, h802, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
          · linarith only [h799, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h806 | h806
          · rcases p613_3 (m.d 3 4) (by simp) with h807 | h807
            · linarith only [h807, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h809 | h809
              · linarith only [h798, h809, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h809, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
          · linarith only [h806, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h813 | h813
        · rcases p613_3 (m.d 2 4) (by simp) with h814 | h814
          · rcases p613_3 (m.d 3 4) (by simp) with h815 | h815
            · linarith only [h815, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h817 | h817
              · linarith only [h797, h817, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h813, h817, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
          · linarith only [h814, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h821 | h821
          · rcases p613_3 (m.d 3 4) (by simp) with h822 | h822
            · linarith only [h822, hlam, p613_0]
            · rcases p613_3 (m.d 4 5) (by simp) with h824 | h824
              · linarith only [h797, h824, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h824, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
          · linarith only [h821, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h829 | h829
      · linarith only [h829, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h831 | h831
        · rcases p613_3 (m.d 2 4) (by simp) with h832 | h832
          · rcases p613_3 (m.d 3 4) (by simp) with h833 | h833
            · rcases p613_3 (m.d 4 5) (by simp) with h834 | h834
              · linarith only [h834, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h831, h834, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
            · linarith only [h833, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h838 | h838
            · rcases p613_3 (m.d 4 5) (by simp) with h839 | h839
              · linarith only [h839, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h839, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p613_1, u5ehi4]
            · linarith only [h838, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h843 | h843
          · rcases p613_3 (m.d 3 4) (by simp) with h844 | h844
            · rcases p613_3 (m.d 4 5) (by simp) with h845 | h845
              · linarith only [h845, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h843, h845, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
            · linarith only [h844, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h849 | h849
            · rcases p613_3 (m.d 4 5) (by simp) with h850 | h850
              · linarith only [h850, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h850, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p613_1, u5ehi4]
            · linarith only [h849, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h854 | h854
      · rcases p613_3 (m.d 1 4) (by simp) with h855 | h855
        · linarith only [h855, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h857 | h857
          · rcases p613_3 (m.d 3 4) (by simp) with h858 | h858
            · rcases p613_3 (m.d 4 5) (by simp) with h859 | h859
              · linarith only [h859, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h854, h859, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · linarith only [h858, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h863 | h863
            · rcases p613_3 (m.d 4 5) (by simp) with h864 | h864
              · linarith only [h864, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h864, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p613_1, u5ehi4]
            · linarith only [h863, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h868 | h868
        · linarith only [h868, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h870 | h870
          · rcases p613_3 (m.d 3 4) (by simp) with h871 | h871
            · rcases p613_3 (m.d 4 5) (by simp) with h872 | h872
              · linarith only [h854, h872, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h870, h872, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p613_1, u5ehi4]
            · linarith only [h871, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h876 | h876
            · rcases p613_3 (m.d 4 5) (by simp) with h877 | h877
              · linarith only [h854, h877, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h877, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p613_1, u5ehi4]
            · linarith only [h876, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      rcases p613_3 (m.d 0 4) (by simp) with h881 | h881
      · rcases p613_3 (m.d 1 4) (by simp) with h882 | h882
        · rcases p613_3 (m.d 2 4) (by simp) with h883 | h883
          · linarith only [h883, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h885 | h885
            · rcases p613_3 (m.d 4 5) (by simp) with h886 | h886
              · linarith only [h886, hc45, hlam, hphi, p613_1, u4ehi2]
              · linarith only [h881, h886, hc04, hlam, hphi, ht0b, ht5b, p613_1, u5ehi4]
            · linarith only [h885, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h890 | h890
          · linarith only [h890, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h892 | h892
            · rcases p613_3 (m.d 4 5) (by simp) with h893 | h893
              · linarith only [h882, h893, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h893, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p613_1, u5ehi4]
            · linarith only [h892, hlam, p613_0]
      · rcases p613_3 (m.d 1 4) (by simp) with h897 | h897
        · rcases p613_3 (m.d 2 4) (by simp) with h898 | h898
          · linarith only [h898, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h900 | h900
            · rcases p613_3 (m.d 4 5) (by simp) with h901 | h901
              · linarith only [h881, h901, hc45, hlam, hphi, p613_1, u4ehi0]
              · linarith only [h897, h901, hc14, hlam, hphi, ht01, ht0b, ht5b, p613_1, u5ehi4]
            · linarith only [h900, hlam, p613_0]
        · rcases p613_3 (m.d 2 4) (by simp) with h905 | h905
          · linarith only [h905, hlam, p613_0]
          · rcases p613_3 (m.d 3 4) (by simp) with h907 | h907
            · rcases p613_3 (m.d 4 5) (by simp) with h908 | h908
              · linarith only [h897, h908, hc45, hlam, hphi, p613_1, u4ehi1]
              · linarith only [h908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p613_1, u5ehi4]
            · linarith only [h907, hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hlam, p613_0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p613_1, u5ehi4]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc45, hlam, hphi, p613_1, u4ehi0]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc45, hlam, hphi, p613_1, u4ehi1]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc45, hlam, hphi, p613_1, u4ehi2]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hc45, hlam, hphi, p613_1, u4ehi3]
    · have p613_0 := h613c.1
      have p613_1 := h613c.2.1
      have p613_2 := h613c.2.2.1
      have p613_3 := h613c.2.2.2
      linarith only [hlam, p613_0]
  · rcases h4bigk with h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h921 | h921
      · rcases p919_3 (m.d 1 4) (by simp) with h922 | h922
        · linarith only [h922, hlam, p919_0]
        · rcases p919_3 (m.d 2 4) (by simp) with h924 | h924
          · rcases p919_3 (m.d 3 4) (by simp) with h925 | h925
            · rcases p919_3 (m.d 4 5) (by simp) with h926 | h926
              · linarith only [h926, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h926, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
            · rcases p919_3 (m.d 4 5) (by simp) with h929 | h929
              · linarith only [h929, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h929, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
          · rcases p919_3 (m.d 3 4) (by simp) with h932 | h932
            · rcases p919_3 (m.d 4 5) (by simp) with h933 | h933
              · linarith only [h933, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h933, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
            · rcases p919_3 (m.d 4 5) (by simp) with h936 | h936
              · linarith only [h936, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h936, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
      · linarith only [h921, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h940 | h940
      · rcases p919_3 (m.d 1 4) (by simp) with h941 | h941
        · linarith only [h0, h941, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi2]
        · rcases p919_3 (m.d 2 4) (by simp) with h943 | h943
          · linarith only [h943, hlam, p919_0]
          · rcases p919_3 (m.d 3 4) (by simp) with h945 | h945
            · rcases p919_3 (m.d 4 5) (by simp) with h946 | h946
              · linarith only [h946, hc45, hlam, hphi, p919_1, u4ehi2]
              · linarith only [h946, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
            · rcases p919_3 (m.d 4 5) (by simp) with h949 | h949
              · linarith only [h949, hc45, hlam, hphi, p919_1, u4ehi2]
              · linarith only [h949, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
      · linarith only [h940, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h953 | h953
      · rcases p919_3 (m.d 1 4) (by simp) with h954 | h954
        · linarith only [h0, h954, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi3]
        · rcases p919_3 (m.d 2 4) (by simp) with h956 | h956
          · rcases p919_3 (m.d 3 4) (by simp) with h957 | h957
            · linarith only [h957, hlam, p919_0]
            · rcases p919_3 (m.d 4 5) (by simp) with h959 | h959
              · linarith only [h959, hc45, hlam, hphi, p919_1, u4ehi3]
              · linarith only [h959, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
          · rcases p919_3 (m.d 3 4) (by simp) with h962 | h962
            · linarith only [h962, hlam, p919_0]
            · rcases p919_3 (m.d 4 5) (by simp) with h964 | h964
              · linarith only [h956, h964, hc45, hlam, hphi, p919_1, u4ehi2]
              · linarith only [h964, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
      · linarith only [h953, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi2]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi3]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p919_1, u5ehi4]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h974 | h974
      · linarith only [h974, hlam, p919_0]
      · rcases p919_3 (m.d 1 4) (by simp) with h976 | h976
        · linarith only [h0, h976, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi0]
        · rcases p919_3 (m.d 2 4) (by simp) with h978 | h978
          · rcases p919_3 (m.d 3 4) (by simp) with h979 | h979
            · rcases p919_3 (m.d 4 5) (by simp) with h980 | h980
              · linarith only [h980, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h980, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
            · rcases p919_3 (m.d 4 5) (by simp) with h983 | h983
              · linarith only [h983, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h983, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
          · linarith only [h978, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h987 | h987
      · rcases p919_3 (m.d 1 4) (by simp) with h988 | h988
        · linarith only [h988, hlam, p919_0]
        · rcases p919_3 (m.d 2 4) (by simp) with h990 | h990
          · rcases p919_3 (m.d 3 4) (by simp) with h991 | h991
            · rcases p919_3 (m.d 4 5) (by simp) with h992 | h992
              · linarith only [h992, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h987, h992, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
            · rcases p919_3 (m.d 4 5) (by simp) with h995 | h995
              · linarith only [h995, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h995, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
          · linarith only [h990, hlam, p919_0]
      · rcases p919_3 (m.d 1 4) (by simp) with h999 | h999
        · linarith only [h999, hlam, p919_0]
        · rcases p919_3 (m.d 2 4) (by simp) with h1001 | h1001
          · rcases p919_3 (m.d 3 4) (by simp) with h1002 | h1002
            · rcases p919_3 (m.d 4 5) (by simp) with h1003 | h1003
              · linarith only [h1003, h987, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1003, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
            · rcases p919_3 (m.d 4 5) (by simp) with h1006 | h1006
              · linarith only [h1006, h987, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1006, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
          · linarith only [h1001, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h1011 | h1011
      · rcases p919_3 (m.d 1 4) (by simp) with h1012 | h1012
        · linarith only [h0, h1012, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi3]
        · rcases p919_3 (m.d 2 4) (by simp) with h1014 | h1014
          · rcases p919_3 (m.d 3 4) (by simp) with h1015 | h1015
            · linarith only [h1015, hlam, p919_0]
            · rcases p919_3 (m.d 4 5) (by simp) with h1017 | h1017
              · linarith only [h1017, hc45, hlam, hphi, p919_1, u4ehi3]
              · linarith only [h1011, h1017, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
          · linarith only [h1014, hlam, p919_0]
      · rcases p919_3 (m.d 1 4) (by simp) with h1021 | h1021
        · linarith only [h0, h1011, h1021, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi0]
        · rcases p919_3 (m.d 2 4) (by simp) with h1023 | h1023
          · rcases p919_3 (m.d 3 4) (by simp) with h1024 | h1024
            · linarith only [h1024, hlam, p919_0]
            · rcases p919_3 (m.d 4 5) (by simp) with h1026 | h1026
              · linarith only [h1011, h1026, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1026, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
          · linarith only [h1023, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h1031 | h1031
      · linarith only [h1031, hlam, p919_0]
      · rcases p919_3 (m.d 1 4) (by simp) with h1033 | h1033
        · linarith only [h0, h1033, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi0]
        · rcases p919_3 (m.d 2 4) (by simp) with h1035 | h1035
          · rcases p919_3 (m.d 3 4) (by simp) with h1036 | h1036
            · rcases p919_3 (m.d 4 5) (by simp) with h1037 | h1037
              · linarith only [h1037, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1037, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p919_1, u5ehi4]
            · linarith only [h1036, hlam, p919_0]
          · rcases p919_3 (m.d 3 4) (by simp) with h1041 | h1041
            · rcases p919_3 (m.d 4 5) (by simp) with h1042 | h1042
              · linarith only [h1042, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1042, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p919_1, u5ehi4]
            · linarith only [h1041, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h1046 | h1046
      · rcases p919_3 (m.d 1 4) (by simp) with h1047 | h1047
        · linarith only [h1047, hlam, p919_0]
        · rcases p919_3 (m.d 2 4) (by simp) with h1049 | h1049
          · rcases p919_3 (m.d 3 4) (by simp) with h1050 | h1050
            · rcases p919_3 (m.d 4 5) (by simp) with h1051 | h1051
              · linarith only [h1051, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h1046, h1051, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
            · linarith only [h1050, hlam, p919_0]
          · rcases p919_3 (m.d 3 4) (by simp) with h1055 | h1055
            · rcases p919_3 (m.d 4 5) (by simp) with h1056 | h1056
              · linarith only [h1056, hc45, hlam, hphi, p919_1, u4ehi1]
              · linarith only [h1056, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p919_1, u5ehi4]
            · linarith only [h1055, hlam, p919_0]
      · rcases p919_3 (m.d 1 4) (by simp) with h1060 | h1060
        · linarith only [h1060, hlam, p919_0]
        · rcases p919_3 (m.d 2 4) (by simp) with h1062 | h1062
          · rcases p919_3 (m.d 3 4) (by simp) with h1063 | h1063
            · rcases p919_3 (m.d 4 5) (by simp) with h1064 | h1064
              · linarith only [h1046, h1064, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1062, h1064, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p919_1, u5ehi4]
            · linarith only [h1063, hlam, p919_0]
          · rcases p919_3 (m.d 3 4) (by simp) with h1068 | h1068
            · rcases p919_3 (m.d 4 5) (by simp) with h1069 | h1069
              · linarith only [h1046, h1069, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1069, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p919_1, u5ehi4]
            · linarith only [h1068, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      rcases p919_3 (m.d 0 4) (by simp) with h1073 | h1073
      · rcases p919_3 (m.d 1 4) (by simp) with h1074 | h1074
        · linarith only [h0, h1074, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi2]
        · rcases p919_3 (m.d 2 4) (by simp) with h1076 | h1076
          · linarith only [h1076, hlam, p919_0]
          · rcases p919_3 (m.d 3 4) (by simp) with h1078 | h1078
            · rcases p919_3 (m.d 4 5) (by simp) with h1079 | h1079
              · linarith only [h1079, hc45, hlam, hphi, p919_1, u4ehi2]
              · linarith only [h1073, h1079, hc04, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
            · linarith only [h1078, hlam, p919_0]
      · rcases p919_3 (m.d 1 4) (by simp) with h1083 | h1083
        · linarith only [h0, h1073, h1083, hlam, hphi, ht01, ht0b, ht45, ht5b, p919_1, u4ehi0]
        · rcases p919_3 (m.d 2 4) (by simp) with h1085 | h1085
          · linarith only [h1085, hlam, p919_0]
          · rcases p919_3 (m.d 3 4) (by simp) with h1087 | h1087
            · rcases p919_3 (m.d 4 5) (by simp) with h1088 | h1088
              · linarith only [h1073, h1088, hc45, hlam, hphi, p919_1, u4ehi0]
              · linarith only [h1088, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p919_1, u5ehi4]
            · linarith only [h1087, hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hlam, p919_0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p919_1, u5ehi4]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hc45, hlam, hphi, p919_1, u4ehi0]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hc45, hlam, hphi, p919_1, u4ehi1]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hc45, hlam, hphi, p919_1, u4ehi2]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hc45, hlam, hphi, p919_1, u4ehi3]
    · have p919_0 := h919c.1
      have p919_1 := h919c.2.1
      have p919_2 := h919c.2.2.1
      have p919_3 := h919c.2.2.2
      linarith only [hlam, p919_0]
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]

theorem n7l_sAB1_M_IR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h5ehi := hb5.2.1
  have h1elo := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · rcases m.htr 0 1 4 (by decide) (by decide) with h10 | h10
                · linarith only [h10, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h10, hlam, p0_0]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                · linarith only [h13, h9, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h13, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h16 | h16
            · linarith only [h16, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h18 | h18
              · rcases m.htr 0 1 4 (by decide) (by decide) with h19 | h19
                · linarith only [h19, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h19, hlam, p0_0]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
                · linarith only [h18, h22, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h22, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h28 | h28
              · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
                · linarith only [h29, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h29, hlam, p0_0]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h32 | h32
                · linarith only [h28, h32, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h32, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h35, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h37 | h37
              · rcases m.htr 0 1 4 (by decide) (by decide) with h38 | h38
                · linarith only [h38, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h38, hlam, p0_0]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h41 | h41
                · linarith only [h37, h41, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h41, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
    · rcases p0_3 (m.d 1 4) (by simp) with h46 | h46
      · linarith only [h46, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi2]
      · rcases p0_3 (m.d 2 4) (by simp) with h48 | h48
        · linarith only [h48, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · rcases p0_3 (m.d 4 5) (by simp) with h51 | h51
            · linarith only [h51, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h53 | h53
              · rcases m.htr 0 1 4 (by decide) (by decide) with h54 | h54
                · linarith only [h54, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi2]
                · linarith only [h46, h53, h54, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h57 | h57
                · linarith only [h53, h57, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h46, h50, h57, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h46, h60, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 1 4 (by decide) (by decide) with h63 | h63
                · linarith only [h46, h63, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h46, h62, h63, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
                · linarith only [h62, h66, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h46, h66, hlam, p0_1]
    · linarith only [h45, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · linarith only [h71, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h73 | h73
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · linarith only [h74, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h78 | h78
              · rcases m.htr 0 1 4 (by decide) (by decide) with h79 | h79
                · linarith only [h79, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi3]
                · linarith only [h71, h73, h79, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h82 | h82
                · linarith only [h78, h82, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h71, h73, h82, hc01, hc24, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h85 | h85
          · linarith only [h85, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h71, h87, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 1 4 (by decide) (by decide) with h90 | h90
                · linarith only [h71, h90, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h71, h89, h90, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h93 | h93
                · linarith only [h89, h93, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h71, h93, hlam, p0_1]
    · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h97 | h97
    · rcases p0_3 (m.d 1 4) (by simp) with h98 | h98
      · linarith only [h98, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h100 | h100
        · rcases p0_3 (m.d 3 4) (by simp) with h101 | h101
          · rcases p0_3 (m.d 4 5) (by simp) with h102 | h102
            · linarith only [h102, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h104 | h104
              · rcases m.htr 0 1 4 (by decide) (by decide) with h105 | h105
                · linarith only [h105, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi4]
                · linarith only [h100, h105, h98, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
                · linarith only [h104, h108, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h100, h108, h98, hc01, hc24, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h111 | h111
            · linarith only [h111, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h113 | h113
              · rcases m.htr 0 1 4 (by decide) (by decide) with h114 | h114
                · linarith only [h101, h114, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi3]
                · linarith only [h100, h114, h98, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h117 | h117
                · linarith only [h113, h117, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h100, h117, h98, hc01, hc24, hlam, hphi, ht12, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h120 | h120
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h121, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
              · rcases m.htr 0 1 4 (by decide) (by decide) with h124 | h124
                · linarith only [h100, h124, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi2]
                · linarith only [h120, h124, h98, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h127 | h127
                · linarith only [h123, h127, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h120, h127, h98, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h130 | h130
            · linarith only [h130, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h132 | h132
              · rcases m.htr 0 1 4 (by decide) (by decide) with h133 | h133
                · linarith only [h100, h133, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi2]
                · linarith only [h132, h133, h98, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h136 | h136
                · linarith only [h132, h136, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h136, h98, hlam, p0_1]
    · linarith only [h97, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h145 | h145
    · linarith only [h145, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h147 | h147
      · linarith only [h147, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h149 | h149
        · rcases p0_3 (m.d 3 4) (by simp) with h150 | h150
          · rcases p0_3 (m.d 4 5) (by simp) with h151 | h151
            · linarith only [h151, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h153 | h153
              · rcases m.htr 0 1 4 (by decide) (by decide) with h154 | h154
                · rcases m.htr 0 1 5 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h156 | h156
                    · linarith only [h156, hlam, p0_0]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h158 | h158
                      · linarith only [h150, h156, h158, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
                        · linarith only [h150, h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                        · linarith only [h151, h160, hlam]
                  · linarith only [h154, h155, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h147, h154, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h165 | h165
                · linarith only [h153, h165, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h147, h165, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h170 | h170
              · rcases m.htr 0 1 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 0 1 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h173 | h173
                    · linarith only [h173, hlam, p0_0]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
                      · linarith only [h173, h175, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                        · linarith only [h177, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                        · linarith only [h168, h177, hlam]
                  · linarith only [h171, h172, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h147, h171, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h182 | h182
                · linarith only [h170, h182, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h147, h182, hlam]
        · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h186 | h186
    · rcases p0_3 (m.d 1 4) (by simp) with h187 | h187
      · linarith only [h187, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h189 | h189
        · rcases p0_3 (m.d 3 4) (by simp) with h190 | h190
          · rcases p0_3 (m.d 4 5) (by simp) with h191 | h191
            · linarith only [h191, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
              · rcases m.htr 0 1 4 (by decide) (by decide) with h194 | h194
                · linarith only [h186, h194, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h186, h193, h194, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h197 | h197
                · linarith only [h193, h197, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h190, h197, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h200 | h200
            · linarith only [h200, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h202 | h202
              · rcases m.htr 0 1 4 (by decide) (by decide) with h203 | h203
                · linarith only [h186, h203, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h203, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h206 | h206
                · linarith only [h202, h206, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h206, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h189, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h210 | h210
      · linarith only [h210, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h212 | h212
        · rcases p0_3 (m.d 3 4) (by simp) with h213 | h213
          · rcases p0_3 (m.d 4 5) (by simp) with h214 | h214
            · linarith only [h186, h214, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h216 | h216
              · rcases m.htr 0 1 4 (by decide) (by decide) with h217 | h217
                · linarith only [h186, h217, hlam]
                · linarith only [h213, h216, h217, hc12, hc34, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h220 | h220
                · linarith only [h186, h220, hlam]
                · linarith only [h213, h220, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h223 | h223
            · linarith only [h223, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h225 | h225
              · rcases m.htr 0 1 4 (by decide) (by decide) with h226 | h226
                · linarith only [h186, h226, hlam]
                · linarith only [h225, h226, hc12, hc24, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h229 | h229
                · linarith only [h186, h229, hlam]
                · linarith only [h229, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h212, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h234 | h234
    · rcases p0_3 (m.d 1 4) (by simp) with h235 | h235
      · linarith only [h235, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h237 | h237
        · rcases p0_3 (m.d 3 4) (by simp) with h238 | h238
          · linarith only [h238, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h240 | h240
            · linarith only [h240, hc45, hlam, hphi, p0_1, u4ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h242 | h242
              · rcases m.htr 0 1 4 (by decide) (by decide) with h243 | h243
                · linarith only [h234, h243, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi3]
                · linarith only [h235, h243, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h246 | h246
                · linarith only [h242, h246, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h235, h246, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h237, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h250 | h250
      · linarith only [h234, h250, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h252 | h252
        · rcases p0_3 (m.d 3 4) (by simp) with h253 | h253
          · linarith only [h253, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h255 | h255
            · linarith only [h234, h255, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h257 | h257
              · rcases m.htr 0 1 4 (by decide) (by decide) with h258 | h258
                · rcases m.htr 0 1 5 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h260 | h260
                    · linarith only [h234, h258, h260, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
                      · linarith only [h234, h260, h262, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                        · linarith only [h234, h264, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
                        · linarith only [h255, h260, h264, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h258, h259, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h250, h258, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h269 | h269
                · linarith only [h257, h269, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h250, h269, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h252, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h273 | h273
    · rcases p0_3 (m.d 1 4) (by simp) with h274 | h274
      · linarith only [h274, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h276 | h276
        · rcases p0_3 (m.d 3 4) (by simp) with h277 | h277
          · rcases p0_3 (m.d 4 5) (by simp) with h278 | h278
            · linarith only [h278, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h280 | h280
              · rcases m.htr 0 1 4 (by decide) (by decide) with h281 | h281
                · linarith only [h273, h281, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi4]
                · linarith only [h274, h281, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h284 | h284
                · linarith only [h280, h284, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h274, h284, hc01, hc24, hlam, hphi, ht12, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h289 | h289
              · rcases m.htr 0 1 4 (by decide) (by decide) with h290 | h290
                · linarith only [h273, h277, h290, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi3]
                · linarith only [h274, h290, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h293 | h293
                · linarith only [h289, h293, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h274, h293, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h276, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h297 | h297
      · linarith only [h273, h297, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h299 | h299
        · rcases p0_3 (m.d 3 4) (by simp) with h300 | h300
          · rcases p0_3 (m.d 4 5) (by simp) with h301 | h301
            · linarith only [h301, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h303 | h303
              · rcases m.htr 0 1 4 (by decide) (by decide) with h304 | h304
                · rcases m.htr 0 1 5 (by decide) (by decide) with h305 | h305
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h306 | h306
                    · linarith only [h273, h304, h306, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h308 | h308
                      · linarith only [h273, h300, h306, h308, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h310 | h310
                        · linarith only [h273, h310, hlam]
                        · linarith only [h300, h304, h310, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                  · linarith only [h304, h305, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h297, h300, h304, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h315 | h315
                · linarith only [h303, h315, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h297, h300, h315, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h318 | h318
            · linarith only [h318, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h320 | h320
              · rcases m.htr 0 1 4 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 1 5 (by decide) (by decide) with h322 | h322
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h323 | h323
                    · linarith only [h300, h323, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi3]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h325 | h325
                      · linarith only [h273, h323, h325, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h327 | h327
                        · linarith only [h273, h327, hlam]
                        · linarith only [h323, h327, hc02, hc24, hlam, hphi, p0_1]
                  · linarith only [h321, h322, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h297, h321, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h332 | h332
                · linarith only [h320, h332, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h297, h332, hc01, hc24, hlam, hphi, ht12, p0_1]
        · linarith only [h299, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h336 | h336
    · linarith only [h336, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h338 | h338
      · linarith only [h338, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h340 | h340
        · rcases p0_3 (m.d 3 4) (by simp) with h341 | h341
          · rcases p0_3 (m.d 4 5) (by simp) with h342 | h342
            · linarith only [h342, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h344 | h344
              · rcases m.htr 0 1 4 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 1 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h347 | h347
                    · linarith only [h340, h344, h345, h347, hc01, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h349 | h349
                      · linarith only [h340, h347, h349, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
                        · linarith only [h351, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                        · linarith only [h342, h351, hlam]
                  · linarith only [h345, h346, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h338, h345, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h356 | h356
                · linarith only [h344, h356, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h338, h356, hlam]
          · linarith only [h341, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h360 | h360
          · rcases p0_3 (m.d 4 5) (by simp) with h361 | h361
            · linarith only [h361, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h363 | h363
              · rcases m.htr 0 1 4 (by decide) (by decide) with h364 | h364
                · rcases m.htr 0 1 5 (by decide) (by decide) with h365 | h365
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h366 | h366
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h367 | h367
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
                        · linarith only [h368, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
                        · linarith only [h361, h368, hlam]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h371 | h371
                        · linarith only [h371, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi4]
                        · linarith only [h361, h371, hlam]
                    · linarith only [h340, h366, hlam]
                  · linarith only [h364, h365, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h338, h364, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h377 | h377
                · linarith only [h363, h377, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h338, h377, hlam]
          · linarith only [h360, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h381 | h381
    · rcases p0_3 (m.d 1 4) (by simp) with h382 | h382
      · linarith only [h382, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h384 | h384
        · rcases p0_3 (m.d 3 4) (by simp) with h385 | h385
          · rcases p0_3 (m.d 4 5) (by simp) with h386 | h386
            · linarith only [h386, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h388 | h388
              · rcases m.htr 0 1 4 (by decide) (by decide) with h389 | h389
                · linarith only [h381, h389, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h381, h388, h389, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h392 | h392
                · linarith only [h388, h392, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h392, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h385, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h396 | h396
          · rcases p0_3 (m.d 4 5) (by simp) with h397 | h397
            · linarith only [h397, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h399 | h399
              · rcases m.htr 0 1 4 (by decide) (by decide) with h400 | h400
                · linarith only [h381, h400, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi1]
                · linarith only [h400, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h403 | h403
                · linarith only [h399, h403, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h403, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h396, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h407 | h407
      · linarith only [h407, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h409 | h409
        · rcases p0_3 (m.d 3 4) (by simp) with h410 | h410
          · rcases p0_3 (m.d 4 5) (by simp) with h411 | h411
            · linarith only [h381, h411, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h413 | h413
              · rcases m.htr 0 1 4 (by decide) (by decide) with h414 | h414
                · linarith only [h381, h414, hlam]
                · linarith only [h413, h414, hc12, hc34, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h417 | h417
                · linarith only [h381, h417, hlam]
                · linarith only [h417, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h410, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h421 | h421
          · rcases p0_3 (m.d 4 5) (by simp) with h422 | h422
            · linarith only [h422, hc45, hlam, hphi, p0_1, u4ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 1 4 (by decide) (by decide) with h425 | h425
                · linarith only [h381, h425, hlam]
                · linarith only [h424, h425, hc12, hc34, hlam, hphi, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h428 | h428
                · linarith only [h381, h428, hlam]
                · linarith only [h428, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h421, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h432 | h432
    · rcases p0_3 (m.d 1 4) (by simp) with h433 | h433
      · linarith only [h433, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi2]
      · rcases p0_3 (m.d 2 4) (by simp) with h435 | h435
        · linarith only [h435, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h437 | h437
          · rcases p0_3 (m.d 4 5) (by simp) with h438 | h438
            · linarith only [h438, hc45, hlam, hphi, p0_1, u4ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h440 | h440
              · rcases m.htr 0 1 4 (by decide) (by decide) with h441 | h441
                · linarith only [h432, h441, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi2]
                · linarith only [h433, h441, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h444 | h444
                · linarith only [h440, h444, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h433, h444, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h437, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h448 | h448
      · linarith only [h432, h448, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h450 | h450
        · linarith only [h450, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h452 | h452
          · rcases p0_3 (m.d 4 5) (by simp) with h453 | h453
            · linarith only [h432, h453, hc45, hlam, hphi, p0_1, u4ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h455 | h455
              · rcases m.htr 0 1 4 (by decide) (by decide) with h456 | h456
                · rcases m.htr 0 1 5 (by decide) (by decide) with h457 | h457
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h458 | h458
                    · linarith only [h432, h458, hlam]
                    · linarith only [h455, h458, hc12, hc34, hlam, hphi, ht23, p0_1]
                  · linarith only [h456, h457, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h448, h456, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h463 | h463
                · linarith only [h455, h463, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h448, h463, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h452, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h468 | h468
    · rcases p0_3 (m.d 1 4) (by simp) with h469 | h469
      · linarith only [h469, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h471 | h471
        · rcases p0_3 (m.d 3 4) (by simp) with h472 | h472
          · rcases p0_3 (m.d 4 5) (by simp) with h473 | h473
            · linarith only [h473, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h475 | h475
              · rcases m.htr 0 1 4 (by decide) (by decide) with h476 | h476
                · linarith only [h468, h476, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi4]
                · linarith only [h469, h471, h476, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h479 | h479
                · linarith only [h475, h479, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h469, h471, h479, hc01, hc24, hlam, hphi, ht12, p0_1]
          · linarith only [h472, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h483 | h483
          · rcases p0_3 (m.d 4 5) (by simp) with h484 | h484
            · linarith only [h484, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h486 | h486
              · rcases m.htr 0 1 4 (by decide) (by decide) with h487 | h487
                · linarith only [h468, h471, h487, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0, u4ehi2]
                · linarith only [h469, h487, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h490 | h490
                · linarith only [h486, h490, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h469, h490, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h483, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h494 | h494
      · linarith only [h468, h494, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h496 | h496
        · rcases p0_3 (m.d 3 4) (by simp) with h497 | h497
          · rcases p0_3 (m.d 4 5) (by simp) with h498 | h498
            · linarith only [h498, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h500 | h500
              · rcases m.htr 0 1 4 (by decide) (by decide) with h501 | h501
                · rcases m.htr 0 1 5 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h503 | h503
                    · linarith only [h468, h496, h501, h503, hc02, hlam, hphi, ht0b, ht45, ht5b, p0_1, u4ehi1]
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h505 | h505
                      · linarith only [h468, h496, h503, h505, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi2]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h507 | h507
                        · linarith only [h468, h507, hlam]
                        · linarith only [h503, h507, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · linarith only [h501, h502, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h494, h501, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h512 | h512
                · linarith only [h500, h512, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h494, h512, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h497, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h516 | h516
          · rcases p0_3 (m.d 4 5) (by simp) with h517 | h517
            · linarith only [h517, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h519 | h519
              · rcases m.htr 0 1 4 (by decide) (by decide) with h520 | h520
                · rcases m.htr 0 1 5 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 0 2 5 (by decide) (by decide) with h523 | h523
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h524 | h524
                        · linarith only [h468, h524, hlam]
                        · linarith only [h524, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi0]
                      · rcases m.htr 0 4 5 (by decide) (by decide) with h527 | h527
                        · linarith only [h468, h527, hlam]
                        · linarith only [h520, h527, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u4ehi1]
                    · linarith only [h496, h522, hc02, hc34, hlam, hphi, ht23, p0_1]
                  · linarith only [h520, h521, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
                · linarith only [h494, h520, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h533 | h533
                · linarith only [h519, h533, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h494, h533, hc01, hc34, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h516, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB1_M_IR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h1ehi := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h15, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h10, h12, h15, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                            · linarith only [h0, h18, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                              · linarith only [h12, h20, hc24, hlam, hphi, ht12, u1ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                                · linarith only [h10, h12, h22, hlam]
                                · rcases h4bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    rcases p24_3 (m.d 0 4) (by simp) with h26 | h26
                                    · rcases p24_3 (m.d 1 4) (by simp) with h27 | h27
                                      · linarith only [h2, h27, hlam]
                                      · rcases p24_3 (m.d 2 4) (by simp) with h29 | h29
                                        · linarith only [h29, h4, hlam]
                                        · rcases p24_3 (m.d 3 4) (by simp) with h31 | h31
                                          · linarith only [h31, h5, hlam]
                                          · rcases p24_3 (m.d 4 5) (by simp) with h33 | h33
                                            · linarith only [h33, h6, hlam]
                                            · linarith only [h12, h33, hlam]
                                    · linarith only [h2, h26, hlam]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    rcases p24_3 (m.d 0 4) (by simp) with h37 | h37
                                    · rcases p24_3 (m.d 1 4) (by simp) with h38 | h38
                                      · linarith only [h2, h38, hlam]
                                      · linarith only [h38, h8, hlam]
                                    · linarith only [h37, h4, hlam]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    rcases p24_3 (m.d 0 4) (by simp) with h42 | h42
                                    · rcases p24_3 (m.d 1 4) (by simp) with h43 | h43
                                      · linarith only [h2, h43, hlam]
                                      · linarith only [h10, h43, hlam]
                                    · linarith only [h42, h5, hlam]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h0, h12, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p24_1, u1ehi3]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h2, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h12, hc45, hlam, hphi, p24_1, u4ehi2]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h12, hc45, hlam, hphi, p24_1, u4ehi3]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h12, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h4, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h8, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h18, hlam, p24_1]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h20, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h5, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h10, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h1, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p24_1, u4ehi2]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h22, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h6, hlam, p24_0]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p24_1, u4ehi1]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p24_1, u4ehi2]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p24_1, u4ehi3]
                                  · have p24_0 := h24c.1
                                    have p24_1 := h24c.2.1
                                    have p24_2 := h24c.2.2.1
                                    have p24_3 := h24c.2.2.2
                                    linarith only [hlam, p24_0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                          · linarith only [h10, h11, h68, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                            · linarith only [h0, h7, h70, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h10, h11, h70, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h1, h10, h5, h73, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                            · linarith only [h10, h76, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                              · linarith only [h0, h78, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h2, h75, h78, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h0, h10, h4, h6, h7, h75, h81, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h10, h75, h83, hc24, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h10, h75, h85, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                · linarith only [h0, h10, h4, h6, h85, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                        · linarith only [h7, h89, h9, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                          · linarith only [h7, h88, h9, h91, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                            · linarith only [h0, h7, h93, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h88, h89, h93, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
                        · linarith only [h1, h5, h88, h96, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                          · linarith only [h8, h9, h98, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                            · linarith only [h0, h100, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                              · linarith only [h102, h88, h98, hc24, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h102, h4, h6, h8, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                    · linarith only [h0, h105, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                      · linarith only [h0, h107, h4, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h0, h109, h4, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                            · linarith only [h107, h112, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                                · rcases h4bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h0, h111, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p116_1, u4ehi4]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h0, h105, h114, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p116_1, u1ehi2]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h0, h107, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p116_1, u1ehi2]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    rcases p116_3 (m.d 0 4) (by simp) with h121 | h121
                                    · rcases p116_3 (m.d 1 4) (by simp) with h122 | h122
                                      · linarith only [h122, h2, hlam]
                                      · linarith only [h111, h122, hlam]
                                    · linarith only [h121, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h2, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h8, hlam, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h107, hlam, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p116_1, u4ehi4]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h4, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h112, hc34, hlam, hphi, ht12, ht23, p116_1, u1ehi3]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h112, hlam, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h1, h112, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p116_1, u4ehi4]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h5, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h1, h111, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p116_1, u4ehi4]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h1, h5, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p116_1, u1ehi2]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h1, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p116_1, u4ehi4]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h6, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h111, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h114, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h115, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                · linarith only [h111, h115, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h111, h114, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                            · linarith only [h107, h148, h7, hc12, hlam, hphi, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                              · linarith only [h1, h111, h148, h150, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                              · linarith only [h0, h150, h4, h6, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
                              · linarith only [h153, h159, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · linarith only [h157, h159, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h154, h158, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                              · linarith only [h153, h157, h164, hc12, hlam, hphi, u1ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                                · linarith only [h157, h166, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                · rcases h4bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    rcases p168_3 (m.d 0 4) (by simp) with h170 | h170
                                    · rcases p168_3 (m.d 1 4) (by simp) with h171 | h171
                                      · linarith only [h171, h2, hlam]
                                      · rcases p168_3 (m.d 2 4) (by simp) with h173 | h173
                                        · linarith only [h173, h4, hlam]
                                        · rcases p168_3 (m.d 3 4) (by simp) with h175 | h175
                                          · linarith only [h175, h5, hlam]
                                          · rcases p168_3 (m.d 4 5) (by simp) with h177 | h177
                                            · linarith only [h177, h6, hlam]
                                            · linarith only [h157, h177, hlam]
                                    · linarith only [h170, h2, hlam]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    rcases p168_3 (m.d 0 4) (by simp) with h181 | h181
                                    · rcases p168_3 (m.d 1 4) (by simp) with h182 | h182
                                      · linarith only [h182, h2, hlam]
                                      · linarith only [h153, h182, hlam]
                                    · linarith only [h181, h4, hlam]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    rcases p168_3 (m.d 0 4) (by simp) with h186 | h186
                                    · rcases p168_3 (m.d 1 4) (by simp) with h187 | h187
                                      · linarith only [h187, h2, hlam]
                                      · linarith only [h155, h187, hlam]
                                    · linarith only [h186, h5, hlam]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h0, h157, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p168_1, u1ehi3]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h2, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h157, h163, hc45, hlam, hphi, p168_1, u4ehi3]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h0, h157, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p168_1, u4ehi3]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h157, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h4, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h153, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h154, h164, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p168_1, u4ehi3]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h164, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h5, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h155, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h163, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h166, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h6, hlam, p168_0]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p168_1, u4ehi1]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p168_1, u4ehi2]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p168_1, u4ehi3]
                                  · have p168_0 := h168c.1
                                    have p168_1 := h168c.2.1
                                    have p168_2 := h168c.2.2.1
                                    have p168_3 := h168c.2.2.2
                                    linarith only [hlam, p168_0]
                            · linarith only [h0, h154, h157, h163, h4, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht5b, u1ehi3, u5ehi2]
                        · linarith only [h154, h156, h7, hlam]
                      · linarith only [h1, h153, h155, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
                          · linarith only [h153, h154, h217, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h220 | h220
                              · linarith only [h217, h220, hc24, hlam, hphi, ht12, u1ehi3]
                              · linarith only [h0, h153, h154, h220, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h0, h153, h217, h219, h4, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, u1ehi3, u4ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                          · linarith only [h153, h216, h224, h7, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                              · linarith only [h153, h224, h227, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                              · linarith only [h0, h153, h154, h227, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h0, h153, h224, h226, h4, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, u1ehi3, u4ehi2]
                      · linarith only [h1, h153, h215, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                    · linarith only [h0, h153, h232, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h235 | h235
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                                · linarith only [h1, h234, h239, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h2, h236, h239, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h153, h236, h238, hlam]
                            · linarith only [h237, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                              · linarith only [h0, h153, h236, h245, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h0, h153, h245, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h2, h234, h235, h244, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h249 | h249
                          · linarith only [h234, h235, h249, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h252 | h252
                              · linarith only [h0, h249, h252, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                              · linarith only [h0, h153, h252, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h251, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h256 | h256
                        · linarith only [h1, h234, h256, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                            · linarith only [h234, h259, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h259, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
                            · linarith only [h234, h262, h7, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h262, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h268 | h268
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h269 | h269
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h270 | h270
                          · linarith only [h2, h270, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                            · linarith only [h0, h265, h272, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h274 | h274
                              · linarith only [h2, h274, h6, hc24, hlam, hphi, ht12, u1ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h276 | h276
                                · linarith only [h2, h268, h276, h6, hc13, hlam, hphi, u1ehi3]
                                · rcases h4bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, p278_1, u1ehi3]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h6, hc45, hlam, hphi, p278_1, u4ehi2]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h6, hc45, hlam, hphi, p278_1, u4ehi3]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h6, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h2, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi2]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h2, h6, hc45, hlam, hphi, p278_1, u4ehi3]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h270, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h4, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h266, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h272, hlam, p278_1]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h274, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h5, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h268, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h1, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi2]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [h276, hlam, p278_0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hc45, hlam, hphi, p278_1, u4ehi0]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p278_1, u1ehi3]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hc45, hlam, hphi, p278_1, u4ehi2]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hc45, hlam, hphi, p278_1, u4ehi3]
                                  · have p278_0 := h278c.1
                                    have p278_1 := h278c.2.1
                                    have p278_2 := h278c.2.2.1
                                    have p278_3 := h278c.2.2.2
                                    linarith only [hlam, p278_0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h304 | h304
                          · linarith only [h2, h304, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                            · linarith only [h0, h265, h306, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h268, h269, h306, hc23, hc35, hlam, hphi]
                      · linarith only [h268, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h310 | h310
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h311 | h311
                        · linarith only [h265, h267, h311, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h313 | h313
                          · linarith only [h2, h313, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                            · linarith only [h0, h265, h315, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h310, h311, h315, hc23, hc35, hlam, hphi]
                      · linarith only [h310, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · linarith only [h266, h4, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h320 | h320
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h322 | h322
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h323 | h323
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                          · linarith only [h2, h324, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                              · linarith only [h2, h320, h327, h6, hc12, hlam, hphi, u1ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                                · linarith only [h2, h329, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                · rcases h4bigk with h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, p331_1, u1ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h326, h6, hc45, hlam, hphi, p331_1, u4ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h6, hc45, hlam, hphi, p331_1, u4ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h6, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h2, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h2, h326, hc01, hlam, hphi, ht0b, ht45, ht5b, p331_1, u4ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h2, h6, hc45, hlam, hphi, p331_1, u4ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h324, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h4, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h320, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p331_1, u4ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h327, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h5, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h322, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h326, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [h329, hlam, p331_0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hc45, hlam, hphi, p331_1, u4ehi0]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p331_1, u1ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hc45, hlam, hphi, p331_1, u4ehi2]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hc45, hlam, hphi, p331_1, u4ehi3]
                                  · have p331_0 := h331c.1
                                    have p331_1 := h331c.2.1
                                    have p331_2 := h331c.2.2.1
                                    have p331_3 := h331c.2.2.2
                                    linarith only [hlam, p331_0]
                            · linarith only [h265, h321, h326, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h265, h321, h323, hlam]
                      · linarith only [h265, h321, h322, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                          · linarith only [h2, h362, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h365 | h365
                              · linarith only [h2, h320, h365, h6, hc12, hlam, hphi, u1ehi3]
                              · linarith only [h320, h321, h365, hc45, hlam, hphi, u4ehi2]
                            · linarith only [h265, h320, h364, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                          · linarith only [h2, h369, h6, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h372 | h372
                              · linarith only [h265, h320, h361, h372, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                              · linarith only [h320, h321, h372, hc45, hlam, hphi, u4ehi2]
                            · linarith only [h265, h320, h371, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h360, h5, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · linarith only [h320, h4, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h378 | h378
              · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
                · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h382 | h382
                      · linarith only [h1, h382, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                            · linarith only [h0, h379, h386, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h388 | h388
                              · linarith only [h0, h380, h388, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h2, h385, h388, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h378, h385, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                            · linarith only [h1, h393, h5, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
                              · linarith only [h0, h380, h395, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h2, h392, h395, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h378, h392, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                      · linarith only [h1, h378, h399, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h401 | h401
                        · linarith only [h380, h381, h399, h401, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                          · linarith only [h380, h381, h403, hlam]
                          · linarith only [h378, h399, h403, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                    · linarith only [h0, h380, h4, h406, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                      · linarith only [h0, h379, h380, h4, h408, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h410 | h410
                        · linarith only [h0, h379, h380, h4, h410, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                            · linarith only [h379, h380, h4, h413, h5, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                                · rcases h4bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h412, hc04, hlam, hphi, ht0b, ht45, ht5b, p417_1, u4ehi4]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h379, h406, h415, h5, hc34, hlam, hphi, ht12, ht23, p417_1, u1ehi2]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h5, hlam, p417_1]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    rcases p417_3 (m.d 0 4) (by simp) with h422 | h422
                                    · rcases p417_3 (m.d 1 4) (by simp) with h423 | h423
                                      · linarith only [h2, h423, hlam]
                                      · linarith only [h412, h423, hlam]
                                    · linarith only [h422, hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h2, hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h380, hlam, p417_1]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h408, hlam, p417_1]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p417_1, u4ehi4]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h4, hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p417_1, u4ehi1]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h413, hlam, p417_1]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p417_1, u4ehi4]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h0, h2, h379, h4, h406, h412, h415, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p417_1, u1ehi2, u4ehi4]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h0, h379, h4, h406, h412, h415, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p417_1, u1ehi2, u4ehi4]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h379, h406, h415, hc34, hlam, hphi, ht12, ht23, p417_1, u1ehi2]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    rcases p417_3 (m.d 0 4) (by simp) with h441 | h441
                                    · linarith only [h441, h5, hlam]
                                    · linarith only [h378, h441, hlam]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h378, hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h412, hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h415, hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [h416, hlam, p417_0]
                                  · have p417_0 := h417c.1
                                    have p417_1 := h417c.2.1
                                    have p417_2 := h417c.2.2.1
                                    have p417_3 := h417c.2.2.2
                                    linarith only [hlam, p417_0]
                                · linarith only [h2, h412, h416, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h380, h412, h415, hlam]
                          · linarith only [h378, h412, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                      · linarith only [h1, h454, h5, hlam]
                      · linarith only [h379, h452, h454, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
                      · linarith only [h1, h457, h5, hlam]
                      · linarith only [h379, h452, h457, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                    · linarith only [h0, h4, h452, h460, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                      · linarith only [h1, h462, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h464 | h464
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                            · linarith only [h0, h1, h4, h452, h464, h466, h5, hc01, hc23, hlam, hphi, ht0b, ht12, ht5b, u1ehi1, u5ehi3]
                            · linarith only [h379, h466, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h378, h462, h464, h465, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                            · linarith only [h4, h452, h471, h5, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h379, h471, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h378, h470, h5, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                · rcases m.htr 1 2 4 (by decide) (by decide) with h476 | h476
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h477 | h477
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h478 | h478
                      · linarith only [h1, h478, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
                          · linarith only [h1, h378, h480, h481, h5, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h478, h480, h481, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h484 | h484
                          · linarith only [h1, h378, h484, h5, hc14, hlam, hphi, u1ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
                            · linarith only [h1, h475, h486, h5, hc12, hlam, hphi, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h488 | h488
                              · linarith only [h1, h378, h488, h5, hc24, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h490 | h490
                                · linarith only [h1, h378, h490, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                · linarith only [h1, h490, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                      · linarith only [h1, h493, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                        · linarith only [h475, h477, h495, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h497 | h497
                          · linarith only [h2, h378, h497, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h499 | h499
                            · linarith only [h1, h499, h5, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h501 | h501
                              · linarith only [h3, h378, h476, h477, h501, hc05, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                              · linarith only [h476, h477, h501, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h378, h4, h476, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                  · linarith only [h1, h378, h475, h5, h505, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h378, h4, h505, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h508 | h508
            · rcases m.htr 0 4 5 (by decide) (by decide) with h509 | h509
              · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
                · rcases m.htr 1 2 4 (by decide) (by decide) with h511 | h511
                  · linarith only [h0, h4, h511, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h514 | h514
                      · linarith only [h510, h511, h514, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h516 | h516
                        · linarith only [h508, h514, h516, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h518 | h518
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                            · linarith only [h0, h510, h514, h519, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                            · linarith only [h4, h508, h519, hlam]
                          · linarith only [h4, h509, h518, hc24, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h523 | h523
                      · linarith only [h510, h511, h523, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h525 | h525
                        · linarith only [h1, h508, h523, h525, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h528 | h528
                            · linarith only [h510, h513, h523, h528, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h4, h508, h528, hlam]
                          · linarith only [h4, h509, h527, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
                  · linarith only [h4, h509, h510, h532, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h539 | h539
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h540 | h540
                                · linarith only [h1, h535, h540, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h0, h4, h534, h539, h540, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                              · linarith only [h1, h4, h535, h537, h539, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h510, h534, h538, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h4, h509, h537, hc24, hlam, hphi, ht12, u1ehi3]
                        · linarith only [h510, h534, h536, hlam]
                      · linarith only [h1, h508, h510, h534, h535, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h550 | h550
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h551 | h551
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h552 | h552
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h553 | h553
                                · linarith only [h1, h548, h553, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h2, h550, h553, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h2, h4, h550, h552, hlam]
                            · linarith only [h4, h508, h510, h551, hc24, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h4, h509, h550, hc24, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
                          · linarith only [h548, h549, h559, hlam]
                          · linarith only [h4, h509, h559, hc24, hlam, hphi, ht12, u1ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h562 | h562
                        · linarith only [h1, h508, h548, h562, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h564 | h564
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h565 | h565
                            · linarith only [h548, h565, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h510, h565, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h4, h509, h564, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
                · rcases m.htr 1 2 4 (by decide) (by decide) with h570 | h570
                  · linarith only [h0, h4, h509, h570, hc45, hlam, hphi, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h572 | h572
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
                      · linarith only [h0, h4, h509, h569, h573, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h508, h509, h573, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h576 | h576
                      · linarith only [h0, h4, h509, h569, h576, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h508, h509, h576, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h579 | h579
                  · linarith only [h0, h4, h579, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h583 | h583
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
                          · linarith only [h0, h4, h509, h581, h584, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                          · linarith only [h579, h581, h584, hlam]
                        · linarith only [h0, h4, h509, h581, h582, h583, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h508, h509, h582, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h589 | h589
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h590 | h590
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h591 | h591
                          · linarith only [h0, h4, h509, h591, hc14, hlam, hphi, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
                              · linarith only [h0, h4, h509, h593, h594, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h4, h594, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                            · linarith only [h569, h589, h593, hc14, hlam, hphi, u1ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h598 | h598
                          · linarith only [h2, h509, h598, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h601 | h601
                              · linarith only [h2, h509, h600, h601, hc23, hlam, hphi, ht12, u1ehi3]
                              · linarith only [h0, h4, h601, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                            · linarith only [h589, h590, h600, hc23, hc35, hlam, hphi]
                      · linarith only [h508, h509, h589, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h606 | h606
              · rcases m.htr 1 2 3 (by decide) (by decide) with h607 | h607
                · rcases m.htr 1 2 4 (by decide) (by decide) with h608 | h608
                  · linarith only [h0, h4, h608, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h610 | h610
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h611 | h611
                      · linarith only [h1, h508, h606, h611, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h613 | h613
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h614 | h614
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h615 | h615
                            · linarith only [h0, h1, h4, h508, h607, h613, h615, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h618 | h618
                                · rcases h4bigk with h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h608, h610, hc04, hlam, hphi, ht0b, ht5b, p619_1, u5ehi2]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h4, hlam, p619_1]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h508, hlam, p619_1]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    rcases p619_3 (m.d 0 4) (by simp) with h624 | h624
                                    · rcases p619_3 (m.d 1 4) (by simp) with h625 | h625
                                      · linarith only [h2, h625, hlam]
                                      · linarith only [h614, h625, hlam]
                                    · linarith only [h624, hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h2, hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h608, hlam, p619_1]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h611, hlam, p619_1]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p619_1, u4ehi4]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h2, h615, hc34, hlam, hphi, ht12, ht23, p619_1, u1ehi3]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h615, hc34, hlam, hphi, ht12, ht23, p619_1, u1ehi3]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h615, hlam, p619_1]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    rcases p619_3 (m.d 0 4) (by simp) with h638 | h638
                                    · linarith only [h4, h638, hlam]
                                    · linarith only [h606, h638, hlam]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h0, h4, h607, h613, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p619_1, u4ehi4]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h607, h608, h613, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p619_1, u4ehi4]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h0, h4, h607, h613, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p619_1, u4ehi4]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    rcases p619_3 (m.d 0 4) (by simp) with h645 | h645
                                    · linarith only [h508, h645, hlam]
                                    · linarith only [h606, h645, hlam]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h606, hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h614, hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h617, hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [h618, hlam, p619_0]
                                  · have p619_0 := h619c.1
                                    have p619_1 := h619c.2.1
                                    have p619_2 := h619c.2.2.1
                                    have p619_3 := h619c.2.2.2
                                    linarith only [hlam, p619_0]
                                · linarith only [h1, h508, h613, h617, h618, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · linarith only [h0, h4, h607, h613, h614, h617, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h4, h606, h614, hc24, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h656 | h656
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h657 | h657
                            · linarith only [h0, h508, h607, h657, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h659 | h659
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h660 | h660
                                · rcases h4bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h608, h610, hc04, hlam, hphi, ht0b, ht5b, p661_1, u5ehi2]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h4, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h508, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    rcases p661_3 (m.d 0 4) (by simp) with h666 | h666
                                    · rcases p661_3 (m.d 1 4) (by simp) with h667 | h667
                                      · linarith only [h2, h667, hlam]
                                      · linarith only [h656, h667, hlam]
                                    · linarith only [h666, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h2, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h608, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h611, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p661_1, u4ehi4]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h2, h657, hc34, hlam, hphi, ht12, ht23, p661_1, u1ehi3]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h657, hc34, hlam, hphi, ht12, ht23, p661_1, u1ehi3]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h657, hlam, p661_1]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    rcases p661_3 (m.d 0 4) (by simp) with h680 | h680
                                    · linarith only [h4, h680, hlam]
                                    · linarith only [h606, h680, hlam]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h0, h4, h610, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p661_1, u4ehi4]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h608, h610, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p661_1, u4ehi4]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h0, h4, h610, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p661_1, u4ehi4]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    rcases p661_3 (m.d 0 4) (by simp) with h687 | h687
                                    · linarith only [h508, h687, hlam]
                                    · linarith only [h606, h687, hlam]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h606, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h656, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h659, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [h660, hlam, p661_0]
                                  · have p661_0 := h661c.1
                                    have p661_1 := h661c.2.1
                                    have p661_2 := h661c.2.2.1
                                    have p661_3 := h661c.2.2.2
                                    linarith only [hlam, p661_0]
                                · linarith only [h0, h4, h610, h659, h660, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                              · linarith only [h2, h4, h656, h659, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h4, h606, h656, hc24, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h698 | h698
                      · linarith only [h1, h508, h606, h698, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h700 | h700
                        · linarith only [h607, h610, h700, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h702 | h702
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                            · linarith only [h1, h508, h703, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h705 | h705
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h706 | h706
                                · rcases h4bigk with h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h4, h607, h610, h702, h703, hc23, hc34, hlam, hphi, p707_1]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h4, hlam, p707_1]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h508, hlam, p707_1]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    rcases p707_3 (m.d 0 4) (by simp) with h712 | h712
                                    · rcases p707_3 (m.d 1 4) (by simp) with h713 | h713
                                      · linarith only [h2, h713, hlam]
                                      · linarith only [h702, h713, hlam]
                                    · linarith only [h712, hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h2, hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h608, hlam, p707_1]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h698, hlam, p707_1]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p707_1, u4ehi4]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h2, h703, hc34, hlam, hphi, ht12, ht23, p707_1, u1ehi3]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h703, hc34, hlam, hphi, ht12, ht23, p707_1, u1ehi3]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h703, hlam, p707_1]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    rcases p707_3 (m.d 0 4) (by simp) with h726 | h726
                                    · linarith only [h4, h726, hlam]
                                    · linarith only [h606, h726, hlam]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h3, h606, h607, h610, hc34, hlam, hphi, ht12, ht23, p707_1, u1ehi2]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h702, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p707_1, u4ehi4]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h0, h4, h607, hc34, hlam, hphi, ht12, ht23, p707_1, u1ehi2]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    rcases p707_3 (m.d 0 4) (by simp) with h733 | h733
                                    · linarith only [h508, h733, hlam]
                                    · linarith only [h606, h733, hlam]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h606, hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h702, hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h705, hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [h706, hlam, p707_0]
                                  · have p707_0 := h707c.1
                                    have p707_1 := h707c.2.1
                                    have p707_2 := h707c.2.2.1
                                    have p707_3 := h707c.2.2.2
                                    linarith only [hlam, p707_0]
                                · linarith only [h2, h702, h706, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h2, h4, h607, h702, h705, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · linarith only [h508, h606, h702, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h744 | h744
                  · linarith only [h0, h4, h744, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h746 | h746
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h747 | h747
                      · linarith only [h1, h508, h747, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h750 | h750
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
                            · linarith only [h1, h508, h607, h746, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                            · linarith only [h607, h746, h751, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h508, h606, h750, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h607, h746, h749, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h756 | h756
                      · linarith only [h1, h508, h756, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h758 | h758
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h759 | h759
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h760 | h760
                            · linarith only [h1, h508, h758, h760, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · linarith only [h607, h760, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h508, h606, h759, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                            · linarith only [h1, h508, h765, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h607, h765, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h4, h606, h764, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
                · rcases m.htr 1 2 4 (by decide) (by decide) with h770 | h770
                  · linarith only [h0, h4, h770, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h772 | h772
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h773 | h773
                      · linarith only [h0, h4, h606, h769, h773, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h775 | h775
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h776 | h776
                          · linarith only [h0, h4, h606, h772, h776, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                          · linarith only [h769, h770, h775, h776, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h779 | h779
                          · linarith only [h0, h4, h606, h779, hc14, hlam, hphi, u1ehi1]
                          · linarith only [h770, h772, h779, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h782 | h782
                      · linarith only [h1, h508, h782, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h784 | h784
                        · linarith only [h769, h772, h784, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h786 | h786
                          · linarith only [h0, h4, h606, h786, hc14, hlam, hphi, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h788 | h788
                            · linarith only [h0, h1, h4, h508, h606, h769, h788, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h790 | h790
                              · linarith only [h0, h4, h606, h769, h788, h790, hc23, hc34, hlam, hphi]
                              · linarith only [h0, h4, h769, h790, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
                  · linarith only [h4, h769, h793, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h796 | h796
                      · linarith only [h1, h508, h606, h796, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                          · linarith only [h2, h606, h799, hlam]
                          · linarith only [h793, h795, h799, hlam]
                        · linarith only [h769, h795, h798, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                      · linarith only [h1, h508, h803, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h806 | h806
                          · linarith only [h1, h508, h606, h805, h806, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h803, h805, h806, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h809 | h809
                          · linarith only [h1, h508, h606, h809, hc14, hlam, hphi, u1ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h811 | h811
                            · linarith only [h1, h508, h769, h811, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h769, h811, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h817 | h817
    · linarith only [h0, h817, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h819 | h819
      · linarith only [h0, h819, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h821 | h821
        · linarith only [h0, h821, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h823 | h823
          · rcases m.htr 0 3 4 (by decide) (by decide) with h824 | h824
            · rcases m.htr 0 4 5 (by decide) (by decide) with h825 | h825
              · rcases m.htr 1 2 3 (by decide) (by decide) with h826 | h826
                · rcases m.htr 1 2 4 (by decide) (by decide) with h827 | h827
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h828 | h828
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h829 | h829
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h830 | h830
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h831 | h831
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h832 | h832
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h833 | h833
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h834 | h834
                                · linarith only [h826, h832, h834, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h823, h833, h834, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h837 | h837
                                · linarith only [h832, h833, h837, hlam]
                                · rcases h4bigk with h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h819, hlam, p839_1]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    rcases p839_3 (m.d 0 4) (by simp) with h842 | h842
                                    · rcases p839_3 (m.d 1 4) (by simp) with h843 | h843
                                      · rcases p839_3 (m.d 2 4) (by simp) with h844 | h844
                                        · linarith only [h823, h844, hlam]
                                        · rcases p839_3 (m.d 3 4) (by simp) with h846 | h846
                                          · linarith only [h824, h846, hlam]
                                          · rcases p839_3 (m.d 4 5) (by simp) with h848 | h848
                                            · linarith only [h825, h848, hlam]
                                            · linarith only [h833, h848, hlam]
                                      · linarith only [h827, h843, hlam]
                                    · linarith only [h823, h842, hlam]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    rcases p839_3 (m.d 0 4) (by simp) with h853 | h853
                                    · rcases p839_3 (m.d 1 4) (by simp) with h854 | h854
                                      · rcases p839_3 (m.d 2 4) (by simp) with h855 | h855
                                        · linarith only [h823, h855, hlam]
                                        · linarith only [h832, h855, hlam]
                                      · linarith only [h829, h854, hlam]
                                    · linarith only [h824, h853, hlam]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h817, h824, h826, h832, h833, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p839_1, u4ehi3]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h819, h826, h829, hc12, hlam, hphi, p839_1, u1ehi0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    rcases p839_3 (m.d 0 4) (by simp) with h863 | h863
                                    · linarith only [h819, h863, hlam]
                                    · linarith only [h823, h863, hlam]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    rcases p839_3 (m.d 0 4) (by simp) with h866 | h866
                                    · linarith only [h819, h866, hlam]
                                    · linarith only [h824, h866, hlam]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h826, h829, h832, h833, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p839_1, u4ehi3]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h823, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h827, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h825, h833, hc04, hlam, hphi, ht0b, ht45, ht5b, p839_1, u4ehi3]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h833, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h824, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h829, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h832, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h837, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h825, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h831, hlam, p839_0]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h825, hc04, hlam, hphi, ht0b, ht45, ht5b, p839_1, u4ehi2]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [h819, h825, h826, h829, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p839_1, u4ehi3]
                                  · have p839_0 := h839c.1
                                    have p839_1 := h839c.2.1
                                    have p839_2 := h839c.2.2.1
                                    have p839_3 := h839c.2.2.2
                                    linarith only [hlam, p839_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h885 | h885
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                                · rcases h4bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h819, hlam, p887_1]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h819, h826, h829, h885, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1, u4ehi4]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h819, h826, h829, h832, h885, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1, u4ehi4]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    rcases p887_3 (m.d 0 4) (by simp) with h892 | h892
                                    · rcases p887_3 (m.d 1 4) (by simp) with h893 | h893
                                      · rcases p887_3 (m.d 2 4) (by simp) with h894 | h894
                                        · linarith only [h823, h894, hlam]
                                        · linarith only [h885, h894, hlam]
                                      · linarith only [h831, h893, hlam]
                                    · linarith only [h892, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h819, h826, h829, hc12, hlam, hphi, p887_1, u1ehi0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h826, h829, h885, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1, u4ehi4]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h826, h829, h832, h885, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1, u4ehi4]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    rcases p887_3 (m.d 0 4) (by simp) with h903 | h903
                                    · linarith only [h819, h903, hlam]
                                    · linarith only [h825, h903, hlam]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h823, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h827, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h832, hlam, p887_1]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h0, h823, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1, u4ehi4]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h824, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h829, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h817, h824, h826, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1, u4ehi2]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h817, h824, h826, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1, u4ehi4]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h825, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h831, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h885, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [h886, hlam, p887_0]
                                  · have p887_0 := h887c.1
                                    have p887_1 := h887c.2.1
                                    have p887_2 := h887c.2.2.1
                                    have p887_3 := h887c.2.2.2
                                    linarith only [hlam, p887_0]
                                · linarith only [h0, h823, h885, h886, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h922 | h922
                                · linarith only [h817, h824, h826, h885, h922, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                · rcases h4bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h819, hlam, p924_1]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    rcases p924_3 (m.d 0 4) (by simp) with h927 | h927
                                    · rcases p924_3 (m.d 1 4) (by simp) with h928 | h928
                                      · rcases p924_3 (m.d 2 4) (by simp) with h929 | h929
                                        · linarith only [h823, h929, hlam]
                                        · rcases p924_3 (m.d 3 4) (by simp) with h931 | h931
                                          · linarith only [h824, h931, hlam]
                                          · linarith only [h832, h931, hlam]
                                      · linarith only [h827, h928, hlam]
                                    · linarith only [h823, h927, hlam]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    rcases p924_3 (m.d 0 4) (by simp) with h936 | h936
                                    · rcases p924_3 (m.d 1 4) (by simp) with h937 | h937
                                      · rcases p924_3 (m.d 2 4) (by simp) with h938 | h938
                                        · linarith only [h823, h938, hlam]
                                        · rcases p924_3 (m.d 3 4) (by simp) with h940 | h940
                                          · linarith only [h824, h940, hlam]
                                          · rcases p924_3 (m.d 4 5) (by simp) with h942 | h942
                                            · linarith only [h825, h942, hlam]
                                            · linarith only [h922, h942, hlam]
                                      · linarith only [h829, h937, hlam]
                                    · linarith only [h824, h936, hlam]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h819, h826, h829, h832, h922, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p924_1]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h819, h826, h829, hc12, hlam, hphi, p924_1, u1ehi0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    rcases p924_3 (m.d 0 4) (by simp) with h950 | h950
                                    · linarith only [h819, h950, hlam]
                                    · linarith only [h823, h950, hlam]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    rcases p924_3 (m.d 0 4) (by simp) with h953 | h953
                                    · linarith only [h819, h953, hlam]
                                    · linarith only [h824, h953, hlam]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h826, h829, h832, h922, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p924_1]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h823, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h827, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h832, hlam, p924_1]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h885, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h824, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h829, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h825, h922, hc04, hlam, hphi, ht0b, ht45, ht5b, p924_1, u4ehi2]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h922, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h825, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h831, hlam, p924_0]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h819, h825, h826, h829, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p924_1, u4ehi2]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [h819, h825, h826, h829, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p924_1, u4ehi3]
                                  · have p924_0 := h924c.1
                                    have p924_1 := h924c.2.1
                                    have p924_2 := h924c.2.2.1
                                    have p924_3 := h924c.2.2.2
                                    linarith only [hlam, p924_0]
                          · linarith only [h819, h825, h831, hlam]
                        · linarith only [h817, h830, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h817, h829, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h828, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h817, h826, h827, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h826, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h978 | h978
                · rcases m.htr 1 2 4 (by decide) (by decide) with h979 | h979
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h980 | h980
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h983 | h983
                          · linarith only [h819, h825, h978, h981, h983, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h819, h983, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                        · linarith only [h817, h982, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h817, h824, h981, hlam]
                    · linarith only [h0, h980, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h823, h979, hlam]
                · linarith only [h0, h978, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h991 | h991
              · rcases m.htr 1 2 3 (by decide) (by decide) with h992 | h992
                · rcases m.htr 1 2 4 (by decide) (by decide) with h993 | h993
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h994 | h994
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h995 | h995
                      · linarith only [h817, h824, h992, h995, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h817, h995, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h994, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h823, h993, hlam]
                · linarith only [h0, h992, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1001 | h1001
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1002 | h1002
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1003 | h1003
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1004 | h1004
                      · linarith only [h1001, h1004, h817, h824, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h1004, h817, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h1003, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h1002, h823, hlam]
                · linarith only [h0, h1001, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1010 | h1010
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1012 | h1012
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1013 | h1013
                  · linarith only [h0, h1013, h823, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1013, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1012, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1017 | h1017
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1018 | h1018
                  · linarith only [h0, h1018, h823, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1018, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1017, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1022 | h1022
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1023 | h1023
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1024 | h1024
                  · linarith only [h0, h1024, h823, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1024, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1023, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1028 | h1028
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1029 | h1029
                  · linarith only [h0, h1029, h823, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1029, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1028, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAB1_M_IR_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1bigk := hb1.1
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
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                          · linarith only [h0, h10, h14, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · linarith only [h14, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h9, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h7, h8, hlam, hphi, ht45, u4ehi3, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h19, h21, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h21, h23, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h19, h23, h7, hc23, hc34, hlam, hphi]
                    · linarith only [h20, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h27, h28, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                        · linarith only [h19, h30, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                          · linarith only [h0, h32, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h32, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h27, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
              · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                · linarith only [h38, h4, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                      · linarith only [h38, h40, h42, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h4, h42, h44, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                        · linarith only [h4, h40, h42, h44, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h41, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                      · linarith only [h4, h49, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                        · linarith only [h4, h40, h51, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                            · rcases h1bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h37, h53, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                rcases p55_3 (m.d 0 1) (by simp) with h58 | h58
                                · rcases p55_3 (m.d 1 2) (by simp) with h59 | h59
                                  · linarith only [h0, h59, hlam]
                                  · linarith only [h4, h59, hlam]
                                · linarith only [h58, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h37, h5, h53, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                rcases p55_3 (m.d 0 1) (by simp) with h64 | h64
                                · rcases p55_3 (m.d 1 2) (by simp) with h65 | h65
                                  · linarith only [h0, h65, hlam]
                                  · linarith only [h37, h65, hlam]
                                · linarith only [h64, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h0, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h4, h49, h5, hc23, hc34, hlam, hphi, p55_1]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h5, hlam, p55_1]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h49, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p55_1, u5ehi6]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h1, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h4, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h38, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h40, hlam, p55_1]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h2, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h37, h53, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p55_1, u4ehi4]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                rcases p55_3 (m.d 0 1) (by simp) with h81 | h81
                                · rcases p55_3 (m.d 1 2) (by simp) with h82 | h82
                                  · linarith only [h5, h82, hlam]
                                  · linarith only [h4, h82, hlam]
                                · linarith only [h1, h81, hlam]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h2, h37, h53, hc01, hlam, hphi, ht0b, ht45, ht5b, p55_1, u4ehi4]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h3, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h37, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h37, h4, h49, h5, h53, hc23, hc34, hlam, hphi, ht45, p55_1, u4ehi4, u5elo1]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [h48, hlam, p55_0]
                              · have p55_0 := h55c.1
                                have p55_1 := h55c.2.1
                                have p55_2 := h55c.2.2.1
                                have p55_3 := h55c.2.2.2
                                linarith only [hlam, p55_0]
                            · linarith only [h37, h49, h5, h53, h54, hlam]
                          · linarith only [h37, h5, h53, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                    · linarith only [h48, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h37, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
            · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
              · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                          · linarith only [h104, h4, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h104, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h103, h4, h98, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h102, h4, h98, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h101, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h100, h4, h97, hlam, hphi, ht45, u4ehi2, u5elo3]
                · linarith only [h4, h97, h99, hlam]
              · linarith only [h97, h98, hlam, hphi, ht45, u4ehi2, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h120 | h120
                            · linarith only [h1, h114, h120, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h113, h117, h119, h120, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h113, h119, h97, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                        · linarith only [h113, h117, h118, h97, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h113, h117, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h116, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h114, h115, hlam, hphi, ht45, u4ehi3, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                      · linarith only [h113, h114, h130, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · linarith only [h113, h130, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h113, h114, h129, h4, hlam, hphi, u5ehi7, u5elo4]
                  · linarith only [h113, h128, h4, hlam, hphi, u5ehi7, u5elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                            · linarith only [h1, h135, h141, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h141, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h137, h140, h97, hlam]
                        · linarith only [h135, h136, h139, h3, h4, hlam, hphi, ht45, u4ehi1, u5elo0]
                      · linarith only [h135, h138, h4, hlam]
                    · linarith only [h137, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h135, h136, hlam, hphi, ht45, u4ehi3, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                      · linarith only [h135, h149, h151, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                            · rcases h1bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                rcases p156_3 (m.d 0 1) (by simp) with h158 | h158
                                · rcases p156_3 (m.d 1 2) (by simp) with h159 | h159
                                  · linarith only [h159, hlam, p156_0]
                                  · rcases p156_3 (m.d 1 3) (by simp) with h161 | h161
                                    · linarith only [h1, h161, hlam]
                                    · linarith only [h161, h4, hlam]
                                · linarith only [h158, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h149, h155, hc01, hlam, hphi, ht0b, ht45, ht5b, p156_1, u4ehi4]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h135, h149, h155, hc01, hlam, hphi, ht0b, ht45, ht5b, p156_1, u4ehi4]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                rcases p156_3 (m.d 0 1) (by simp) with h167 | h167
                                · rcases p156_3 (m.d 1 2) (by simp) with h168 | h168
                                  · linarith only [h0, h168, hlam]
                                  · rcases p156_3 (m.d 1 3) (by simp) with h170 | h170
                                    · linarith only [h1, h170, hlam]
                                    · linarith only [h149, h170, hlam]
                                · linarith only [h167, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h0, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h4, hlam, p156_1]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h97, hlam, p156_1]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h113, hlam, p156_1]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h1, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h135, hc12, hc34, hlam, hphi, ht23, p156_1]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h135, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h135, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p156_1, u5ehi6]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h2, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                rcases p156_3 (m.d 0 1) (by simp) with h185 | h185
                                · rcases p156_3 (m.d 1 2) (by simp) with h186 | h186
                                  · linarith only [h186, h97, hlam]
                                  · rcases p156_3 (m.d 1 3) (by simp) with h188 | h188
                                    · linarith only [h135, h188, hlam]
                                    · linarith only [h188, h4, hlam]
                                · linarith only [h0, h185, hlam]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h149, h155, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p156_1, u4ehi4]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h149, h155, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p156_1, u4ehi4]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h3, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h149, h151, h155, h4, hc12, hc34, hlam, hphi, ht23, ht45, p156_1, u4ehi4, u5elo1]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h149, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [h150, hlam, p156_0]
                              · have p156_0 := h156c.1
                                have p156_1 := h156c.2.1
                                have p156_2 := h156c.2.2.1
                                have p156_3 := h156c.2.2.2
                                linarith only [hlam, p156_0]
                            · linarith only [h149, h151, h155, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h150, h154, h3, hlam, hphi, ht45, u4ehi2, u5elo0]
                        · linarith only [h149, h153, h4, hlam]
                    · linarith only [h150, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h204 | h204
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                            · rcases h1bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h211 | h211
                                · rcases p209_3 (m.d 1 2) (by simp) with h212 | h212
                                  · linarith only [h212, hlam, p209_0]
                                  · rcases p209_3 (m.d 1 3) (by simp) with h214 | h214
                                    · linarith only [h1, h214, hlam]
                                    · linarith only [h214, h4, hlam]
                                · linarith only [h211, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h218 | h218
                                · rcases p209_3 (m.d 1 2) (by simp) with h219 | h219
                                  · linarith only [h0, h219, hlam]
                                  · rcases p209_3 (m.d 1 3) (by simp) with h221 | h221
                                    · linarith only [h221, hlam, p209_0]
                                    · rcases p209_3 (m.d 1 4) (by simp) with h223 | h223
                                      · linarith only [h2, h223, hlam]
                                      · linarith only [h135, h223, hlam]
                                · linarith only [h218, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h204, hc01, hlam, hphi, ht0b, ht45, ht5b, p209_1, u4ehi4]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                rcases p209_3 (m.d 0 1) (by simp) with h228 | h228
                                · rcases p209_3 (m.d 1 2) (by simp) with h229 | h229
                                  · linarith only [h0, h229, hlam]
                                  · rcases p209_3 (m.d 1 3) (by simp) with h231 | h231
                                    · linarith only [h1, h231, hlam]
                                    · rcases p209_3 (m.d 1 4) (by simp) with h233 | h233
                                      · linarith only [h2, h233, hlam]
                                      · linarith only [h204, h233, hlam]
                                · linarith only [h228, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h0, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h4, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h97, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h113, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h1, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h149, h206, hc12, hlam, hphi, ht23, ht34, ht45, p209_1, u5elo2]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h135, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h149, hlam, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h2, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h135, h205, hc12, hc23, hlam, hphi, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h135, h205, h4, hc12, hc23, hlam, hphi, p209_1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h135, h205, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p209_1, u5ehi6]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h3, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p209_1, u5elo1]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h149, h206, h4, hc12, hlam, hphi, ht23, ht34, ht45, p209_1, u5elo2]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [h204, hlam, p209_0]
                              · have p209_0 := h209c.1
                                have p209_1 := h209c.2.1
                                have p209_2 := h209c.2.2.1
                                have p209_3 := h209c.2.2.2
                                linarith only [hlam, p209_0]
                            · linarith only [h135, h208, hlam, hphi, ht45, u4ehi1, u5elo4]
                          · linarith only [h135, h204, h205, h207, hlam]
                        · linarith only [h206, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                        · linarith only [h149, h205, h260, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h260, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h204, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h2, h3, hlam, hphi, ht45, u4ehi0, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h265 | h265
        · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
          · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
            · linarith only [h0, h2, h267, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h269 | h269
              · linarith only [h0, h2, h267, h269, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
              · linarith only [h266, h269, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h272 | h272
            · linarith only [h0, h2, h272, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
              · linarith only [h1, h2, h266, h272, h274, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h276 | h276
                · linarith only [h1, h2, h272, h276, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h278 | h278
                  · linarith only [h1, h2, h276, h278, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                      · linarith only [h0, h2, h276, h281, hc12, hc23, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                        · linarith only [h278, h281, h283, hc13, hc34, hlam, hphi]
                        · linarith only [h266, h283, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h2, h265, h280, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
        · linarith only [h0, h265, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h288 | h288
      · rcases m.htr 0 1 5 (by decide) (by decide) with h289 | h289
        · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
          · linarith only [h0, h1, h290, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
            · linarith only [h0, h1, h292, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
              · linarith only [h1, h288, h290, h292, h294, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                    · linarith only [h1, h288, h290, h298, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h298, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h1, h289, h297, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                · linarith only [h1, h288, h296, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
        · linarith only [h288, h289, hlam, hphi, ht45, u4ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h304 | h304
        · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
          · linarith only [h0, h1, h305, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
            · linarith only [h0, h1, h307, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
              · linarith only [h0, h1, h305, h309, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                · rcases m.htr 1 3 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h313 | h313
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h314 | h314
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h315 | h315
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h316 | h316
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h317 | h317
                            · rcases h1bigk with h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h288, h305, h311, hc12, hc23, hlam, hphi, p318_1]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h1, hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h288, hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h288, h305, h311, h312, h317, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p318_1, u4ehi4]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h0, hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h305, hlam, p318_1]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h307, hlam, p318_1]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h309, hlam, p318_1]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h0, h305, hc12, hc23, hlam, hphi, p318_1]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                rcases p318_3 (m.d 0 1) (by simp) with h330 | h330
                                · linarith only [h1, h330, hlam]
                                · linarith only [h0, h330, hlam]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h288, h304, h305, h312, h317, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p318_1, u4ehi4]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                rcases p318_3 (m.d 0 1) (by simp) with h335 | h335
                                · linarith only [h1, h335, hlam]
                                · linarith only [h304, h335, hlam]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h304, h312, h317, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p318_1, u4ehi4]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                rcases p318_3 (m.d 0 1) (by simp) with h339 | h339
                                · linarith only [h288, h339, hlam]
                                · linarith only [h0, h339, hlam]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h311, hlam, p318_1]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                rcases p318_3 (m.d 0 1) (by simp) with h344 | h344
                                · linarith only [h288, h344, hlam]
                                · linarith only [h304, h344, hlam]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h304, hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p318_1, u5elo1]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h312, hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [h313, hlam, p318_0]
                              · have p318_0 := h318c.1
                                have p318_1 := h318c.2.1
                                have p318_2 := h318c.2.2.1
                                have p318_3 := h318c.2.2.2
                                linarith only [hlam, p318_0]
                            · linarith only [h288, h304, h305, h311, h313, h317, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h288, h304, h305, h311, h313, h316, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h288, h304, h305, h311, h312, h315, hlam]
                      · linarith only [h288, h304, h305, h311, h314, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                    · linarith only [h288, h304, h313, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
                  · linarith only [h288, h304, h311, h312, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                · linarith only [h1, h304, h311, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
        · linarith only [h0, h304, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h360 | h360
    · rcases m.htr 0 1 4 (by decide) (by decide) with h361 | h361
      · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
        · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
          · rcases m.htr 1 2 4 (by decide) (by decide) with h364 | h364
            · rcases m.htr 1 2 5 (by decide) (by decide) with h365 | h365
              · rcases m.htr 1 3 4 (by decide) (by decide) with h366 | h366
                · linarith only [h0, h360, h366, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h368 | h368
                  · linarith only [h0, h361, h366, h368, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                    · linarith only [h0, h361, h370, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h370, hlam, hphi, ht45, u4ehi1, u5elo4]
              · linarith only [h0, h362, h365, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h361, h364, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h361, h363, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h361, h362, hlam, hphi, ht45, u4ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h377 | h377
        · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
          · rcases m.htr 1 2 4 (by decide) (by decide) with h379 | h379
            · rcases m.htr 1 2 5 (by decide) (by decide) with h380 | h380
              · rcases m.htr 1 3 4 (by decide) (by decide) with h381 | h381
                · linarith only [h360, h361, h379, h381, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h383 | h383
                  · linarith only [h360, h361, h381, h383, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                      · linarith only [h361, h378, h381, h383, h386, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                        · linarith only [h378, h383, h388, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h390 | h390
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h391 | h391
                            · rcases h1bigk with h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h0, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h361, h378, h381, hc23, hc34, hlam, hphi, p392_1]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h361, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h361, h379, h380, h390, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p392_1, u4ehi4]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h377, h380, h390, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p392_1, u4ehi4]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                rcases p392_3 (m.d 0 1) (by simp) with h400 | h400
                                · linarith only [h0, h400, hlam]
                                · linarith only [h360, h400, hlam]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h361, h377, h380, h390, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p392_1, u4ehi4]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                rcases p392_3 (m.d 0 1) (by simp) with h404 | h404
                                · linarith only [h0, h404, hlam]
                                · linarith only [h377, h404, hlam]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h360, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h378, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h381, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h383, hlam, p392_1]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h377, h380, h390, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p392_1, u4ehi4]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h379, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                rcases p392_3 (m.d 0 1) (by simp) with h414 | h414
                                · linarith only [h361, h414, hlam]
                                · linarith only [h360, h414, hlam]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                rcases p392_3 (m.d 0 1) (by simp) with h418 | h418
                                · linarith only [h361, h418, hlam]
                                · linarith only [h377, h418, hlam]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h377, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h380, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [hc13, hlam, hphi, ht34, ht45, p392_1, u5elo1]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [h385, hlam, p392_0]
                              · have p392_0 := h392c.1
                                have p392_1 := h392c.2.1
                                have p392_2 := h392c.2.2.1
                                have p392_3 := h392c.2.2.2
                                linarith only [hlam, p392_0]
                            · linarith only [h361, h377, h380, h381, h390, h391, hlam]
                          · linarith only [h390, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h361, h385, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h377, h380, hlam, hphi, u5ehi6, u5elo2]
            · linarith only [h0, h377, h379, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h377, h378, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h360, h377, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h433 | h433
      · rcases m.htr 0 1 5 (by decide) (by decide) with h434 | h434
        · rcases m.htr 1 2 3 (by decide) (by decide) with h435 | h435
          · rcases m.htr 1 2 4 (by decide) (by decide) with h436 | h436
            · rcases m.htr 1 2 5 (by decide) (by decide) with h437 | h437
              · rcases m.htr 1 3 4 (by decide) (by decide) with h438 | h438
                · rcases m.htr 1 3 5 (by decide) (by decide) with h439 | h439
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h440 | h440
                    · linarith only [h360, h433, h435, h440, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h440, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h360, h433, h436, h439, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h360, h433, h436, h438, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h360, h433, h435, h436, h437, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h360, h433, h435, h436, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h433, h435, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h433, h434, hlam, hphi, ht45, u4ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h449 | h449
        · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
          · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
            · rcases m.htr 1 2 5 (by decide) (by decide) with h452 | h452
              · rcases m.htr 1 3 4 (by decide) (by decide) with h453 | h453
                · rcases m.htr 1 3 5 (by decide) (by decide) with h454 | h454
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h455 | h455
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h456 | h456
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h459 | h459
                            · linarith only [h450, h456, h459, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h433, h449, h452, h453, h458, h459, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h458, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h456, h457, hlam, hphi, ht45, u4ehi3, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
                        · linarith only [h450, h453, h456, h464, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h466 | h466
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h467 | h467
                            · rcases h1bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h0, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h360, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h433, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h433, h450, h453, h454, h464, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p468_1]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h449, h454, h464, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p468_1]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h453, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p468_1, u4ehi3]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h433, h449, h454, h464, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p468_1]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h478 | h478
                                · linarith only [h0, h478, hlam]
                                · linarith only [h449, h478, hlam]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h449, h454, h464, h466, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p468_1, u4ehi4]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h450, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h433, h449, h450, h454, h464, h466, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p468_1, u4ehi4]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h485 | h485
                                · linarith only [h360, h485, hlam]
                                · linarith only [h449, h485, hlam]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h449, h454, h464, h466, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p468_1, u4ehi4]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h451, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h453, hlam, p468_1]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h492 | h492
                                · linarith only [h433, h492, hlam]
                                · linarith only [h449, h492, hlam]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h449, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h452, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h454, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h455, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                            · linarith only [h456, h466, h467, hlam]
                          · linarith only [h466, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h455, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h360, h454, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h360, h449, h452, h453, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h0, h452, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h360, h449, h450, h451, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h449, h450, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h508 | h508
          · rcases m.htr 1 2 4 (by decide) (by decide) with h509 | h509
            · rcases m.htr 1 2 5 (by decide) (by decide) with h510 | h510
              · rcases m.htr 1 3 4 (by decide) (by decide) with h511 | h511
                · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h515 | h515
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h516 | h516
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h517 | h517
                            · linarith only [h508, h514, h517, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h517, hlam, hphi, ht45, u4ehi3, u5elo4]
                          · linarith only [h516, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h512, h514, h515, hlam, hphi, ht45, u4ehi3, u5elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h522 | h522
                        · linarith only [h508, h511, h514, h522, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h524 | h524
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h525 | h525
                            · rcases h1bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
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
                                linarith only [h360, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h433, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h449, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                rcases p526_3 (m.d 0 1) (by simp) with h532 | h532
                                · linarith only [h532, hlam, p526_0]
                                · rcases p526_3 (m.d 1 2) (by simp) with h534 | h534
                                  · rcases p526_3 (m.d 1 3) (by simp) with h535 | h535
                                    · linarith only [h508, h535, hlam]
                                    · linarith only [h360, h535, hlam]
                                  · linarith only [h534, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h511, h514, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p526_1, u4ehi2]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h433, hc01, hc12, hlam, hphi, p526_1]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h449, hc01, hc12, hlam, hphi, p526_1]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                rcases p526_3 (m.d 0 1) (by simp) with h543 | h543
                                · linarith only [h543, hlam, p526_0]
                                · rcases p526_3 (m.d 1 2) (by simp) with h545 | h545
                                  · rcases p526_3 (m.d 1 3) (by simp) with h546 | h546
                                    · rcases p526_3 (m.d 1 4) (by simp) with h547 | h547
                                      · linarith only [h511, h547, hlam]
                                      · linarith only [h433, h547, hlam]
                                    · linarith only [h546, hlam, p526_0]
                                  · linarith only [h0, h545, hlam]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h508, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h511, h514, h524, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p526_1, u4ehi4]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h449, h508, hc01, hc12, hlam, hphi, p526_1]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                rcases p526_3 (m.d 0 1) (by simp) with h556 | h556
                                · linarith only [h556, hlam, p526_0]
                                · rcases p526_3 (m.d 1 2) (by simp) with h558 | h558
                                  · rcases p526_3 (m.d 1 3) (by simp) with h559 | h559
                                    · rcases p526_3 (m.d 1 4) (by simp) with h560 | h560
                                      · rcases p526_3 (m.d 1 5) (by simp) with h561 | h561
                                        · linarith only [h513, h561, hlam]
                                        · linarith only [h449, h561, hlam]
                                      · linarith only [h560, hlam, p526_0]
                                    · linarith only [h360, h559, hlam]
                                  · linarith only [h0, h558, hlam]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h509, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h511, hlam, p526_1]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h449, hc01, hc14, hlam, hphi, p526_1]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p526_1, u5elo1]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h510, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h512, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [h513, hlam, p526_0]
                              · have p526_0 := h526c.1
                                have p526_1 := h526c.2.1
                                have p526_2 := h526c.2.2.1
                                have p526_3 := h526c.2.2.2
                                linarith only [hlam, p526_0]
                            · linarith only [h514, h524, h525, hlam]
                          · linarith only [h524, hlam, hphi, ht45, u4ehi2, u5elo4]
                    · linarith only [h513, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h360, h512, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h580 | h580
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h581 | h581
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                      · linarith only [h511, h580, h582, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h584 | h584
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h585 | h585
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h586 | h586
                            · rcases h1bigk with h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h0, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h360, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h433, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h449, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                rcases p587_3 (m.d 0 1) (by simp) with h593 | h593
                                · linarith only [h593, hlam, p587_0]
                                · rcases p587_3 (m.d 1 2) (by simp) with h595 | h595
                                  · rcases p587_3 (m.d 1 3) (by simp) with h596 | h596
                                    · linarith only [h508, h596, hlam]
                                    · linarith only [h360, h596, hlam]
                                  · linarith only [h595, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h508, h584, h586, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p587_1, u4ehi4]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h508, h511, h584, h586, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p587_1, u4ehi4]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h449, hc01, hc12, hlam, hphi, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h511, hc01, hc34, hlam, hphi, ht12, ht23, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h508, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h511, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h449, h511, hc01, hc34, hlam, hphi, ht12, ht23, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                rcases p587_3 (m.d 0 1) (by simp) with h609 | h609
                                · linarith only [h609, hlam, p587_0]
                                · rcases p587_3 (m.d 1 2) (by simp) with h611 | h611
                                  · rcases p587_3 (m.d 1 3) (by simp) with h612 | h612
                                    · linarith only [h511, h612, hlam]
                                    · linarith only [h360, h612, hlam]
                                  · linarith only [h0, h611, hlam]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h509, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h360, hc01, hc14, hlam, hphi, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h449, h511, hc01, hc34, hlam, hphi, ht12, ht23, p587_1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p587_1, u5elo1]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h510, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h580, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [h581, hlam, p587_0]
                              · have p587_0 := h587c.1
                                have p587_1 := h587c.2.1
                                have p587_2 := h587c.2.2.1
                                have p587_3 := h587c.2.2.2
                                linarith only [hlam, p587_0]
                            · linarith only [h508, h511, h584, h586, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h581, h585, hlam, hphi, ht45, u4ehi2, u5elo1]
                        · linarith only [h511, h580, h584, hc23, hc34, hlam, hphi]
                    · linarith only [h581, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h360, h580, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h510, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
              · rcases m.htr 1 3 4 (by decide) (by decide) with h632 | h632
                · linarith only [h508, h509, h632, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h636 | h636
                      · linarith only [h632, h634, h636, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h638 | h638
                        · linarith only [h508, h509, h638, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · linarith only [h508, h509, h634, h636, h638, hc23, hc34, hlam, hphi]
                    · linarith only [h635, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h360, h634, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h631, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
            · rcases m.htr 1 2 5 (by decide) (by decide) with h645 | h645
              · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
                · rcases m.htr 1 3 5 (by decide) (by decide) with h647 | h647
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h648 | h648
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h649 | h649
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h650 | h650
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h651 | h651
                          · linarith only [h508, h644, h651, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h651, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h508, h645, h650, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h508, h645, h649, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h433, h648, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h360, h647, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h508, h644, h646, hlam]
              · linarith only [h644, h645, hlam, hphi, ht45, u4ehi2, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
              · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
                · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h665 | h665
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h667 | h667
                            · rcases h1bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h0, hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h360, hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h433, hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h449, hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h644, h664, hc01, hc23, hlam, hphi, ht12, p668_1]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h508, hlam, p668_1]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h644, hlam, p668_1]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h449, h644, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p668_1, u5ehi5]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                rcases p668_3 (m.d 0 1) (by simp) with h679 | h679
                                · linarith only [h679, hlam, p668_0]
                                · rcases p668_3 (m.d 1 2) (by simp) with h681 | h681
                                  · linarith only [h508, h681, hlam]
                                  · linarith only [h0, h681, hlam]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h660, h665, h667, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p668_1, u4ehi4]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h508, h644, h660, h665, h667, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p668_1, u4ehi4]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h449, h508, hc01, hc23, hlam, hphi, ht12, p668_1]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                rcases p668_3 (m.d 0 1) (by simp) with h688 | h688
                                · linarith only [h688, hlam, p668_0]
                                · rcases p668_3 (m.d 1 2) (by simp) with h690 | h690
                                  · linarith only [h644, h690, hlam]
                                  · linarith only [h0, h690, hlam]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h660, h665, h667, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p668_1, u4ehi4]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h661, hlam, p668_1]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h449, h508, h661, hc01, hc23, hlam, hphi, ht12, p668_1]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p668_1, u5elo1]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h660, hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h662, hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [h663, hlam, p668_0]
                              · have p668_0 := h668c.1
                                have p668_1 := h668c.2.1
                                have p668_2 := h668c.2.2.1
                                have p668_3 := h668c.2.2.2
                                linarith only [hlam, p668_0]
                            · linarith only [h644, h660, h664, h666, h667, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h644, h663, h666, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
                        · linarith only [h508, h660, h665, hlam, hphi, u5ehi7, u5elo3]
                      · linarith only [h508, h660, h664, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h663, hlam, hphi, ht45, u4ehi1, u5elo4]
                  · linarith only [h644, h660, h661, h662, hlam, hphi, u5ehi7, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h708 | h708
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                      · linarith only [h661, h708, h710, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · linarith only [h508, h660, h710, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h508, h660, h661, h709, hlam, hphi, u5ehi7, u5elo4]
                  · linarith only [h508, h660, h708, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h0, h660, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

end R2N4
