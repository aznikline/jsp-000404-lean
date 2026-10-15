import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_L_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h2, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h2, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h13, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h13, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h16, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h19 | h19
          · linarith only [h19, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
            · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
              · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h22, h3, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
              · linarith only [h0, h25, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h2, h25, h3, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
        · rcases m.htr 0 3 4 (by decide) (by decide) with h29 | h29
          · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
              · linarith only [h2, h31, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h33, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h28, h33, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
              · linarith only [h2, h36, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                · linarith only [h0, h38, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h28, h38, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h2, h28, h29, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h42 | h42
          · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
              · linarith only [h2, h44, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h28, h46, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h1, h49, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h43, h49, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h42, h48, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h2, h42, h53, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h28, h55, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h1, h43, h58, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                        · linarith only [h0, h28, h43, h61, hc12, hlam, hphi, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                          · linarith only [h0, h28, h42, h61, h63, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases h4bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p65_1, u0elo3]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h28, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1, u0elo3]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h43, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h1, hlam, p65_1]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h55, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p65_1, u0elo0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h58, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h61, hc04, hc45, hlam, hphi, p65_1]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h61, hc14, hc45, hlam, hphi, p65_1]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h61, hc34, hc45, hlam, hphi, p65_1]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h61, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h42, hlam, p65_1]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h57, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h60, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h63, hlam, p65_0]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              rcases p65_3 (m.d 0 4) (by simp) with h86 | h86
                              · linarith only [h86, hlam, p65_0]
                              · rcases p65_3 (m.d 1 4) (by simp) with h88 | h88
                                · linarith only [h58, h88, hlam]
                                · rcases p65_3 (m.d 2 4) (by simp) with h90 | h90
                                  · linarith only [h61, h90, hlam]
                                  · linarith only [h28, h90, hlam]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              rcases p65_3 (m.d 0 4) (by simp) with h93 | h93
                              · linarith only [h43, h93, hlam]
                              · linarith only [h1, h93, hlam]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [h0, h28, hc12, hc45, hlam, hphi, ht23, ht34, p65_1]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              rcases p65_3 (m.d 0 4) (by simp) with h97 | h97
                              · linarith only [h43, h97, hlam]
                              · linarith only [h42, h97, hlam]
                            · have p65_0 := h65c.1
                              have p65_1 := h65c.2.1
                              have p65_2 := h65c.2.2.1
                              have p65_3 := h65c.2.2.2
                              linarith only [hlam, p65_0]
                      · linarith only [h2, h42, h60, hlam]
                  · linarith only [h42, h57, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
            · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
              · linarith only [h0, h104, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                · linarith only [h0, h106, h28, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                  · linarith only [h104, h108, h2, h42, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                    · linarith only [h1, h110, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1, h103, h104, h108, h110, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
              · linarith only [h0, h113, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                · linarith only [h0, h115, h28, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                  · linarith only [h0, h113, h117, h2, h42, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h1, h103, h119, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                      · linarith only [h0, h121, h2, h42, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                        · linarith only [h0, h103, h123, h28, hc12, hlam, hphi, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                          · linarith only [h0, h121, h123, h125, h2, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h121, h125, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h128 | h128
      · rcases m.htr 0 2 4 (by decide) (by decide) with h129 | h129
        · linarith only [h0, h1, h129, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
          · linarith only [h0, h1, h128, h131, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
            · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
              · linarith only [h0, h134, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h1, h128, h134, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
              · linarith only [h0, h1, h133, h137, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
              · linarith only [h128, h129, h137, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h140 | h140
        · linarith only [h0, h1, h140, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
          · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
            · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
              · linarith only [h128, h144, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                · linarith only [h0, h1, h140, h146, hlam]
                · linarith only [h0, h1, h146, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
              · linarith only [h0, h1, h128, h142, h149, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                · linarith only [h0, h151, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h1, h151, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
            · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
              · linarith only [h0, h128, h155, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                · linarith only [h0, h1, h157, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h1, h157, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
              · linarith only [h0, h128, h160, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                · linarith only [h0, h1, h154, h162, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                · linarith only [h0, h1, h162, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h165 | h165
    · rcases m.htr 0 2 3 (by decide) (by decide) with h166 | h166
      · rcases m.htr 0 2 4 (by decide) (by decide) with h167 | h167
        · rcases m.htr 0 3 4 (by decide) (by decide) with h168 | h168
          · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h165, h173, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h165, h169, h173, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h168, h172, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h171, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h170, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                    · linarith only [h165, h169, h182, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                      · linarith only [h166, h184, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h168, h184, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h168, h181, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h180, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h165, h179, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
            · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
              · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
                  · linarith only [h0, h165, h168, h193, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                    · linarith only [h0, h165, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h190, h195, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h192, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h165, h166, h190, h191, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
              · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                  · linarith only [h0, h165, h166, h168, h202, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h204 | h204
                    · linarith only [h0, h165, h190, h204, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                      · linarith only [h166, h168, h206, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h208 | h208
                        · linarith only [h165, h167, h190, h200, h202, h208, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                          · rcases h4bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h200, h202, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p211_1, u0elo3]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h190, h210, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h168, hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h190, hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h165, hlam, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h0, h165, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p211_1, u2elo1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h202, hlam, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h204, hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h167, hlam, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h201, hlam, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h206, hlam, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h208, hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              rcases p211_3 (m.d 0 4) (by simp) with h227 | h227
                              · linarith only [h168, h227, hlam]
                              · rcases p211_3 (m.d 1 4) (by simp) with h229 | h229
                                · linarith only [h202, h229, hlam]
                                · rcases p211_3 (m.d 2 4) (by simp) with h231 | h231
                                  · linarith only [h206, h231, hlam]
                                  · rcases p211_3 (m.d 3 4) (by simp) with h233 | h233
                                    · rcases p211_3 (m.d 4 5) (by simp) with h234 | h234
                                      · linarith only [h210, h234, hlam]
                                      · linarith only [h190, h234, hlam]
                                    · linarith only [h168, h233, hlam]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              rcases p211_3 (m.d 0 4) (by simp) with h238 | h238
                              · linarith only [h168, h238, hlam]
                              · linarith only [h165, h238, hlam]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              rcases p211_3 (m.d 0 4) (by simp) with h241 | h241
                              · linarith only [h168, h241, hlam]
                              · linarith only [h167, h241, hlam]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h165, h190, h200, h202, hc23, hc34, hlam, hphi, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h165, h200, h202, h210, hc23, hc34, hlam, hphi, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h200, h202, h210, hc23, hc34, hlam, hphi, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h206, h210, hc23, hc34, hlam, hphi, p211_1]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [h210, hlam, p211_0]
                            · have p211_0 := h211c.1
                              have p211_1 := h211c.2.1
                              have p211_2 := h211c.2.2.1
                              have p211_3 := h211c.2.2.2
                              linarith only [hlam, p211_0]
                          · rcases h4bigk with h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h200, h202, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p251_1, u0elo3]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h0, h165, h206, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h168, hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h190, hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h165, hlam, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h0, h165, h206, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h202, hlam, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h204, hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h167, hlam, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h201, hlam, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h206, hlam, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h208, hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h210, hc04, hc45, hlam, hphi, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h210, hc14, hc45, hlam, hphi, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h206, h210, hc23, hc45, hlam, hphi, ht34, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h210, hlam, p251_0]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              rcases p251_3 (m.d 0 4) (by simp) with h272 | h272
                              · linarith only [h272, hlam, p251_0]
                              · rcases p251_3 (m.d 1 4) (by simp) with h274 | h274
                                · linarith only [h204, h274, hlam]
                                · rcases p251_3 (m.d 2 4) (by simp) with h276 | h276
                                  · linarith only [h208, h276, hlam]
                                  · rcases p251_3 (m.d 3 4) (by simp) with h278 | h278
                                    · linarith only [h210, h278, hlam]
                                    · linarith only [h168, h278, hlam]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              rcases p251_3 (m.d 0 4) (by simp) with h281 | h281
                              · linarith only [h190, h281, hlam]
                              · linarith only [h165, h281, hlam]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              rcases p251_3 (m.d 0 4) (by simp) with h284 | h284
                              · linarith only [h190, h284, hlam]
                              · linarith only [h167, h284, hlam]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [h166, h168, hc23, hc45, hlam, hphi, ht34, p251_1]
                            · have p251_0 := h251c.1
                              have p251_1 := h251c.2.1
                              have p251_2 := h251c.2.2.1
                              have p251_3 := h251c.2.2.2
                              linarith only [hlam, p251_0]
                · linarith only [h0, h201, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h165, h166, h200, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
        · linarith only [h0, h165, h167, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
        · rcases m.htr 0 3 4 (by decide) (by decide) with h293 | h293
          · rcases m.htr 0 4 5 (by decide) (by decide) with h294 | h294
            · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
              · linarith only [h0, h166, h295, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h165, h294, h295, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
              · linarith only [h0, h166, h298, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h165, h298, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h165, h166, h293, hlam]
        · linarith only [h0, h165, h292, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h303 | h303
      · rcases m.htr 0 2 4 (by decide) (by decide) with h304 | h304
        · rcases m.htr 0 3 4 (by decide) (by decide) with h305 | h305
          · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
            · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
              · rcases m.htr 1 2 4 (by decide) (by decide) with h308 | h308
                · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                      · linarith only [h303, h311, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h305, h311, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h165, h306, h310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h303, h305, h309, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h304, h308, hlam]
              · linarith only [h0, h307, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                · rcases m.htr 1 3 4 (by decide) (by decide) with h320 | h320
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                    · linarith only [h165, h306, h318, h320, h321, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
                      · linarith only [h303, h323, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h305, h323, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h303, h305, h320, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h304, h319, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h318, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
            · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
              · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                      · linarith only [h303, h305, h334, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
                        · linarith only [h304, h336, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h329, h336, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h305, h329, h330, h332, h333, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                      · linarith only [h303, h332, h341, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h343 | h343
                        · linarith only [h304, h343, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h304, h329, h343, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h304, h329, h340, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h331, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h303, h304, h330, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
              · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                    · linarith only [h165, h329, h350, h352, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                      · linarith only [h303, h305, h354, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h356 | h356
                        · linarith only [h165, h352, h356, hc01, hlam, hphi, ht12, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h358 | h358
                          · linarith only [h165, h352, h358, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h4bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h165, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p360_1, u0elo3]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h305, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h329, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h352, hc04, hc45, hlam, hphi, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h352, hc24, hc45, hlam, hphi, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h303, h305, h352, hc23, hc45, hlam, hphi, ht34, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h352, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h304, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h350, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h354, hlam, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h356, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h165, h349, h351, hc01, hlam, hphi, ht12, p360_1, u2elo1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h351, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h349, h351, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p360_1, u2elo1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h358, hlam, p360_0]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 4) (by simp) with h381 | h381
                              · linarith only [h381, hlam, p360_0]
                              · rcases p360_3 (m.d 1 4) (by simp) with h383 | h383
                                · linarith only [h352, h383, hlam]
                                · linarith only [h165, h383, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h165, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              rcases p360_3 (m.d 0 4) (by simp) with h387 | h387
                              · linarith only [h329, h387, hlam]
                              · linarith only [h304, h387, hlam]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [h303, h305, hc23, hc45, hlam, hphi, ht34, p360_1]
                            · have p360_0 := h360c.1
                              have p360_1 := h360c.2.1
                              have p360_2 := h360c.2.2.1
                              have p360_3 := h360c.2.2.2
                              linarith only [hlam, p360_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                    · linarith only [h165, h329, h350, h392, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                      · linarith only [h303, h351, h394, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h396 | h396
                        · linarith only [h304, h396, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h398 | h398
                          · linarith only [h165, h392, h398, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h4bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h165, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p400_1, u0elo3]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h305, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h329, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h351, h398, hc04, hc45, hlam, hphi, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h351, h398, hc24, hc45, hlam, hphi, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h351, hlam, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h392, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h304, hlam, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h350, hlam, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h394, hlam, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h396, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h165, h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h398, hc14, hc45, hlam, hphi, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h398, hc24, hc45, hlam, hphi, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h398, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              rcases p400_3 (m.d 0 4) (by simp) with h421 | h421
                              · linarith only [h421, hlam, p400_0]
                              · rcases p400_3 (m.d 1 4) (by simp) with h423 | h423
                                · linarith only [h392, h423, hlam]
                                · linarith only [h165, h423, hlam]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h165, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              rcases p400_3 (m.d 0 4) (by simp) with h427 | h427
                              · linarith only [h329, h427, hlam]
                              · linarith only [h304, h427, hlam]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h303, h305, hc23, hc45, hlam, hphi, ht34, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                · linarith only [h0, h350, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h303, h349, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h434 | h434
          · linarith only [h303, h304, h434, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
            · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
              · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
                · linarith only [h303, h304, h438, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h438, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h303, h437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h442 | h442
              · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                · linarith only [h304, h443, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h443, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h303, h442, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h447 | h447
        · rcases m.htr 0 3 4 (by decide) (by decide) with h448 | h448
          · rcases m.htr 0 4 5 (by decide) (by decide) with h449 | h449
            · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
              · linarith only [h303, h450, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h450, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h453 | h453
              · linarith only [h303, h447, h453, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h453, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h303, h447, h448, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h457 | h457
          · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
            · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
              · linarith only [h303, h459, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h459, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
              · linarith only [h0, h303, h462, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h462, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h465 | h465
            · rcases m.htr 1 2 3 (by decide) (by decide) with h466 | h466
              · linarith only [h0, h303, h466, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h466, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h469 | h469
              · linarith only [h0, h303, h469, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h469, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_14_H_L_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h2, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h2, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h13, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h13, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h16, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
        · rcases m.htr 0 2 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 0 3 4 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h2, h20, h23, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                · linarith only [h1, h23, h25, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h20, h25, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2, h20, h22, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h29 | h29
            · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h2, h20, h30, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                · linarith only [h0, h32, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h20, h32, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2, h20, h29, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h36 | h36
          · rcases m.htr 0 3 4 (by decide) (by decide) with h37 | h37
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
              · linarith only [h0, h2, h38, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                · linarith only [h0, h20, h36, h40, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h1, h38, h42, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h36, h42, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
              · linarith only [h0, h2, h36, h45, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                · linarith only [h1, h2, h36, h37, h45, h47, hc24, hc25, hlam, hphi, ht0b, ht5b, u0elo0, u4elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h1, h45, h49, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h2, h36, h37, h49, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
            · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h2, h53, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                · linarith only [h1, h20, h53, h55, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h0, h36, h57, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h1, h52, h62, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h61, h62, hc34, hlam, hphi, u4elo2]
                        · linarith only [h0, h20, h61, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                        · linarith only [h59, h60, h66, hlam]
                        · linarith only [h0, h20, h66, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h2, h59, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
              · linarith only [h0, h2, h70, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                · linarith only [h0, h20, h72, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                          · rcases h2bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo1]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h2, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h20, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h36, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h0, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h70, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h72, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h74, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              rcases p80_3 (m.d 0 2) (by simp) with h91 | h91
                              · linarith only [h91, hlam, p80_0]
                              · rcases p80_3 (m.d 1 2) (by simp) with h93 | h93
                                · linarith only [h70, h93, hlam]
                                · rcases p80_3 (m.d 2 3) (by simp) with h95 | h95
                                  · rcases p80_3 (m.d 2 4) (by simp) with h96 | h96
                                    · linarith only [h76, h96, hlam]
                                    · linarith only [h20, h96, hlam]
                                  · linarith only [h95, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              rcases p80_3 (m.d 0 2) (by simp) with h100 | h100
                              · linarith only [h100, h2, hlam]
                              · linarith only [h0, h100, hlam]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h2, h52, h76, hc02, hc23, hlam, hphi, p80_1]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h0, h36, hc12, hc23, hlam, hphi, p80_1]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p80_1, u4elo2]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p80_1, u4elo2]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h76, hlam, p80_1]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h0, h36, hc12, hlam, hphi, ht23, ht34, p80_1, u4elo2]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h0, h78, hc12, hlam, hphi, ht23, ht34, p80_1, u4elo2]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h78, hc12, hlam, hphi, ht23, ht34, p80_1, u4elo2]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h77, hlam, p80_1]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [h78, hlam, p80_0]
                            · have p80_0 := h80c.1
                              have p80_1 := h80c.2.1
                              have p80_2 := h80c.2.2.1
                              have p80_3 := h80c.2.2.2
                              linarith only [hlam, p80_0]
                          · linarith only [h0, h2, h52, h79, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h0, h20, h78, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h2, h52, h76, h77, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h2, h76, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h120 | h120
      · linarith only [h0, h1, h120, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h122 | h122
        · rcases m.htr 0 2 5 (by decide) (by decide) with h123 | h123
          · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
            · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
              · linarith only [h0, h1, h120, h122, h125, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                · linarith only [h0, h1, h127, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h122, h127, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h122, h124, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
            · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
              · linarith only [h0, h120, h122, h132, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h134 | h134
                · linarith only [h0, h1, h134, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h122, h134, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h122, h131, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h138 | h138
          · rcases m.htr 0 3 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
              · linarith only [h0, h120, h138, h140, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                · linarith only [h0, h1, h122, h138, h142, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                  · linarith only [h0, h1, h144, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h138, h144, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h139, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
            · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
              · linarith only [h0, h120, h149, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                · linarith only [h0, h1, h151, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h0, h138, h153, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                          · linarith only [h148, h158, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h157, h158, hc34, hlam, hphi, u4elo2]
                        · linarith only [h0, h122, h157, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h1, h149, h156, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h149, h155, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h1, h148, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h165 | h165
    · rcases m.htr 0 2 3 (by decide) (by decide) with h166 | h166
      · rcases m.htr 0 2 4 (by decide) (by decide) with h167 | h167
        · rcases m.htr 0 2 5 (by decide) (by decide) with h168 | h168
          · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                    · linarith only [h165, h170, h173, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h165, h169, h173, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h168, h172, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h165, h167, h170, h171, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h166, h170, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                    · linarith only [h165, h169, h179, h182, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                      · linarith only [h0, h165, h179, h184, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                        · linarith only [h167, h186, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                          · linarith only [h186, h188, hc24, hlam, hphi, u4elo3]
                          · linarith only [h169, h188, hc03, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h168, h181, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h165, h167, h179, h180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h166, h179, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h194 | h194
            · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
              · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                    · linarith only [h165, h195, h198, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h194, h198, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                    · linarith only [h166, h168, h201, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h165, h168, h194, h201, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h167, h168, h196, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h166, h168, h195, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
              · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
                · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                    · linarith only [h0, h165, h168, h194, h206, h208, h209, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h211 | h211
                      · linarith only [h0, h165, h168, h206, h208, h211, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h213 | h213
                        · linarith only [h167, h168, h208, h213, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h165, h168, h206, h213, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                    · linarith only [h165, h194, h206, h216, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                      · linarith only [h0, h165, h168, h206, h218, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h0, h165, h206, h208, h218, hc23, hc35, hlam, hphi]
                · linarith only [h0, h165, h167, h168, h206, h207, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h165, h166, h168, h206, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
        · linarith only [h166, h167, hc23, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h165, h166, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h225 | h225
      · rcases m.htr 0 2 4 (by decide) (by decide) with h226 | h226
        · rcases m.htr 0 2 5 (by decide) (by decide) with h227 | h227
          · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
            · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
              · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                    · linarith only [h225, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h225, h228, h232, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h165, h227, h229, h231, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h226, h230, hlam]
              · linarith only [h0, h225, h229, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
              · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
                    · linarith only [h225, h228, h241, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                      · linarith only [h225, h243, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                        · linarith only [h226, h245, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                          · linarith only [h245, h247, hc24, hlam, hphi, u4elo3]
                          · linarith only [h228, h247, hc03, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h227, h240, hlam]
                · linarith only [h0, h239, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h225, h238, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
            · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
              · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                · rcases m.htr 1 2 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h257 | h257
                    · linarith only [h225, h227, h257, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h253, h257, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                    · linarith only [h225, h227, h260, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h225, h227, h253, h260, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h226, h227, h255, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h225, h254, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
              · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
                    · linarith only [h225, h227, h253, h268, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
                      · linarith only [h226, h227, h268, h270, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                        · linarith only [h226, h227, h272, hc45, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h226, h227, h268, h272, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h275 | h275
                    · linarith only [h165, h225, h227, h253, h275, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                      · linarith only [h225, h227, h277, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                        · linarith only [h226, h227, h279, hc45, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h0, h267, h279, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h226, h266, hlam]
              · linarith only [h0, h225, h226, h265, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
        · linarith only [h225, h226, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h285 | h285
        · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
          · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
            · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
              · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
                · rcases m.htr 1 2 5 (by decide) (by decide) with h290 | h290
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                        · linarith only [h285, h293, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                          · linarith only [h291, h293, h295, hlam]
                          · rcases h2bigk with h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h0, hlam, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h225, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h225, hc24, hlam, hphi, ht0b, ht45, ht5b, p297_1, u0elo2]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h225, hc25, hlam, hphi, ht0b, ht5b, p297_1, u0elo2]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              rcases p297_3 (m.d 0 2) (by simp) with h303 | h303
                              · linarith only [h0, h303, hlam]
                              · rcases p297_3 (m.d 1 2) (by simp) with h305 | h305
                                · rcases p297_3 (m.d 2 3) (by simp) with h306 | h306
                                  · linarith only [h288, h306, hlam]
                                  · linarith only [h225, h306, hlam]
                                · linarith only [h0, h305, hlam]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h0, h225, hc01, hc12, hlam, hphi, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h225, h286, h288, h293, hlam, p297_2]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h225, h286, h288, hlam, p297_2]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h286, h288, h291, h293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h288, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              rcases p297_3 (m.d 0 2) (by simp) with h317 | h317
                              · linarith only [h225, h317, hlam]
                              · linarith only [h285, h317, hlam]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              rcases p297_3 (m.d 0 2) (by simp) with h320 | h320
                              · linarith only [h225, h320, hlam]
                              · linarith only [h286, h320, hlam]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h285, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h289, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h291, hlam, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h293, hlam, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h286, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h290, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h292, hlam, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h286, h291, hc34, hlam, hphi, ht0b, ht45, ht5b, p297_1, u0elo1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                      · linarith only [h225, h286, h292, hlam]
                    · linarith only [h225, h291, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h286, h290, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h225, h285, h288, h289, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
                · rcases m.htr 1 2 5 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h340 | h340
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h341 | h341
                        · linarith only [h285, h341, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                          · linarith only [h339, h341, h343, hlam]
                          · rcases h2bigk with h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h0, hlam, p345_1]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h225, hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h225, hc24, hlam, hphi, ht0b, ht45, ht5b, p345_1, u0elo2]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h225, hc25, hlam, hphi, ht0b, ht5b, p345_1, u0elo2]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h288, hc02, hc23, hlam, hphi, p345_1]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h288, hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              rcases p345_3 (m.d 0 2) (by simp) with h354 | h354
                              · linarith only [h0, h354, hlam]
                              · linarith only [h285, h354, hlam]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              rcases p345_3 (m.d 0 2) (by simp) with h357 | h357
                              · linarith only [h0, h357, hlam]
                              · linarith only [h286, h357, hlam]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              rcases p345_3 (m.d 0 2) (by simp) with h360 | h360
                              · linarith only [h360, hlam, p345_0]
                              · rcases p345_3 (m.d 1 2) (by simp) with h362 | h362
                                · linarith only [h288, h362, hlam]
                                · linarith only [h0, h362, hlam]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p345_1]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              rcases p345_3 (m.d 0 2) (by simp) with h367 | h367
                              · linarith only [h225, h367, hlam]
                              · linarith only [h285, h367, hlam]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              rcases p345_3 (m.d 0 2) (by simp) with h370 | h370
                              · linarith only [h225, h370, hlam]
                              · linarith only [h286, h370, hlam]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h285, hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h337, hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h339, hlam, p345_1]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h341, hlam, p345_1]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h286, hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h338, hlam, p345_0]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h340, hlam, p345_1]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [h286, h339, hc34, hlam, hphi, ht0b, ht45, ht5b, p345_1, u0elo1]
                            · have p345_0 := h345c.1
                              have p345_1 := h345c.2.1
                              have p345_2 := h345c.2.2.1
                              have p345_3 := h345c.2.2.2
                              linarith only [hlam, p345_0]
                      · linarith only [h0, h288, h340, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h288, h339, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h286, h338, hlam]
                · linarith only [h0, h337, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h225, h285, h287, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h388 | h388
            · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
              · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h392 | h392
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h393 | h393
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h394 | h394
                        · linarith only [h285, h394, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h285, h286, h394, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h397 | h397
                        · linarith only [h285, h397, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h225, h285, h393, h397, hc24, hlam, hphi, u4elo4]
                    · linarith only [h225, h285, h392, hc24, hlam, hphi, u4elo3]
                  · linarith only [h225, h285, h389, h391, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h225, h285, h389, h390, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h403 | h403
                · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                  · linarith only [h285, h286, h389, h404, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                        · linarith only [h285, h408, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h0, h404, h408, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h0, h389, h407, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h389, h406, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h285, h403, hlam]
            · linarith only [h225, h285, h388, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h415 | h415
          · rcases m.htr 0 3 4 (by decide) (by decide) with h416 | h416
            · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
              · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                · rcases m.htr 1 2 5 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h421 | h421
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h422 | h422
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h423 | h423
                          · linarith only [h416, h423, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h418, h422, h423, hc34, hlam, hphi, u4elo1]
                        · linarith only [h285, h422, hc02, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h285, h415, h420, h421, hlam]
                    · linarith only [h225, h415, h420, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h225, h415, h417, h419, hlam]
                · linarith only [h225, h415, h417, h418, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                · linarith only [h285, h415, h417, h431, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h431, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
              · rcases m.htr 1 2 4 (by decide) (by decide) with h435 | h435
                · rcases m.htr 1 2 5 (by decide) (by decide) with h436 | h436
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                    · linarith only [h165, h416, h434, h437, hc01, hc12, hlam, hphi]
                    · linarith only [h225, h415, h437, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h415, h436, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h225, h415, h434, h435, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                · linarith only [h285, h415, h434, h442, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h442, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h445 | h445
            · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
              · rcases m.htr 1 2 4 (by decide) (by decide) with h447 | h447
                · rcases m.htr 1 2 5 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h450 | h450
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h451 | h451
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h452 | h452
                          · linarith only [h445, h452, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h451, h452, hc34, hlam, hphi, u4elo2]
                        · linarith only [h0, h285, h451, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                        · linarith only [h449, h450, h456, hlam]
                        · linarith only [h0, h285, h456, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h225, h449, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h225, h446, h448, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h225, h446, h447, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h462 | h462
                · linarith only [h0, h285, h446, h462, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h462, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
              · rcases m.htr 1 2 4 (by decide) (by decide) with h466 | h466
                · rcases m.htr 1 2 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h468 | h468
                    · linarith only [h165, h445, h465, h468, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h225, h468, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h225, h465, h467, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h225, h465, h466, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                · linarith only [h0, h285, h465, h473, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h473, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

end R2N4
