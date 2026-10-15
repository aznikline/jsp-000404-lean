import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_I_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h2, h5, h6, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h2, h5, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h13, h6, hc45, hlam, hphi, u4ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h2, h5, h6, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, h2, h5, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h2, h20, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h20, h6, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
              · linarith only [h23, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h1, h26, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h0, h2, h29, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h29, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h25, h28, h5, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h1, h33, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h0, h2, h36, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h36, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h0, h2, h39, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h39, hc45, hlam, hphi, u4ehi2]
          · linarith only [h4, hc45, hlam, hphi, u4ehi0]
        · linarith only [h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
          · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
            · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
              · linarith only [h0, h47, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                  · linarith only [h0, h46, h50, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                      · linarith only [h2, h44, h50, h53, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h45, h47, h53, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h0, h49, h56, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h2, h44, h45, h56, hlam]
                · linarith only [h2, h44, h49, hc12, hc24, hlam, hphi]
            · linarith only [h1, h2, h46, hc12, hc24, hlam, hphi]
          · linarith only [h45, hc45, hlam, hphi, u4ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
          · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
              · linarith only [h0, h64, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h44, h62, h66, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                  · linarith only [h1, h2, h68, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h0, h44, h63, h70, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                        · rcases h2bigk with h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h44, h68, h72, hc12, hc34, hlam, hphi, ht23, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h44, h68, h72, hc23, hc34, hlam, hphi, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h2, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h44, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, h44, h68, h72, hc23, hc34, hlam, hphi, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h64, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h66, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h1, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h63, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h68, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h70, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h1, h68, hc23, hc34, hlam, hphi, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h63, h68, hc23, hc34, hlam, hphi, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h92 | h92
                            · linarith only [h2, h92, hlam]
                            · linarith only [h1, h92, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, h44, h63, h68, hc23, hc34, hlam, hphi, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, h63, h70, hc23, hc35, hlam, hphi, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h63, h70, hc23, hc35, hlam, hphi, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h99 | h99
                            · linarith only [h44, h99, hlam]
                            · linarith only [h1, h99, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h72, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                        · linarith only [h62, h68, h73, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h2, h62, h72, hlam]
            · linarith only [h1, h44, h63, hc12, hc25, hlam, hphi]
          · linarith only [h62, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h108 | h108
      · linarith only [h1, h108, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h110 | h110
        · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
          · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
            · linarith only [h0, h1, h110, h112, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
              · linarith only [h0, h108, h114, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                      · linarith only [h108, h110, h117, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h111, h119, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h1, h110, h111, h118, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h1, h110, h111, h117, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · linarith only [h1, h110, h116, hc12, hc23, hlam, hphi]
          · linarith only [h111, hc45, hlam, hphi, u4ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
          · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
            · linarith only [h0, h1, h127, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
              · linarith only [h0, h108, h126, h129, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                · linarith only [h0, h110, h131, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                        · linarith only [h133, h136, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h126, h136, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h126, h135, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h108, h126, h133, h134, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                        · linarith only [h133, h141, h143, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h126, h143, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h108, h142, hc45, hlam, hphi, u4ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                        · rcases h2bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h1, h141, h148, hc12, hc34, hlam, hphi, ht23, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h1, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h108, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h110, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h0, hlam, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h127, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h129, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h131, hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h141, h148, hc02, hc34, hlam, hphi, ht23, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h141, h148, hc12, hc34, hlam, hphi, ht23, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h133, hlam, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h141, hlam, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            rcases p149_3 (m.d 0 2) (by simp) with h165 | h165
                            · linarith only [h165, hlam, p149_0]
                            · rcases p149_3 (m.d 1 2) (by simp) with h167 | h167
                              · linarith only [h129, h167, hlam]
                              · rcases p149_3 (m.d 2 3) (by simp) with h169 | h169
                                · linarith only [h133, h169, hlam]
                                · linarith only [h1, h169, hlam]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            rcases p149_3 (m.d 0 2) (by simp) with h172 | h172
                            · linarith only [h108, h172, hlam]
                            · linarith only [h0, h172, hlam]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h0, h1, h133, hc12, hc34, hlam, hphi, ht23, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h110, h126, h133, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p149_1, u4ehi4]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            rcases p149_3 (m.d 0 2) (by simp) with h178 | h178
                            · linarith only [h178, hlam, p149_0]
                            · rcases p149_3 (m.d 1 2) (by simp) with h180 | h180
                              · linarith only [h131, h180, hlam]
                              · rcases p149_3 (m.d 2 3) (by simp) with h182 | h182
                                · linarith only [h141, h182, hlam]
                                · linarith only [h1, h182, hlam]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            rcases p149_3 (m.d 0 2) (by simp) with h185 | h185
                            · linarith only [h110, h185, hlam]
                            · linarith only [h0, h185, hlam]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h0, h1, hc12, hc25, hlam, hphi, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [h147, hlam, p149_1]
                          · have p149_0 := h149c.1
                            have p149_1 := h149c.2.1
                            have p149_2 := h149c.2.2.1
                            have p149_3 := h149c.2.2.2
                            linarith only [hlam, p149_0]
                        · linarith only [h108, h133, h148, hc45, hlam, hphi, u4ehi0]
                      · linarith only [h108, h126, h147, hlam]
          · linarith only [h126, hc45, hlam, hphi, u4ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h194 | h194
    · rcases m.htr 0 2 4 (by decide) (by decide) with h195 | h195
      · rcases m.htr 0 2 5 (by decide) (by decide) with h196 | h196
        · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
          · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
            · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
              · rcases m.htr 1 2 5 (by decide) (by decide) with h200 | h200
                · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                  · linarith only [h194, h201, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h0, h195, h204, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h197, h204, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                      · linarith only [h0, h195, h207, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h207, hc45, hlam, hphi, u4ehi2]
                · linarith only [h0, h195, h197, h200, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h195, h197, h199, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h194, h198, hlam]
          · linarith only [h197, hc45, hlam, hphi, u4ehi0]
        · linarith only [h195, h196, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h215 | h215
        · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
          · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
            · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
              · linarith only [h195, h216, h218, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h220 | h220
                · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h194, h221, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                      · linarith only [h0, h194, h218, h221, h223, h224, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h216, h218, h224, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                      · linarith only [h0, h215, h218, h221, h227, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h216, h227, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h215, h220, hlam]
            · linarith only [h0, h194, h217, hlam]
          · linarith only [h216, hc45, hlam, hphi, u4ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h233 | h233
          · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
            · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
              · linarith only [h195, h233, h235, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h237 | h237
                · linarith only [h215, h235, h237, hc02, hc24, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                  · linarith only [h194, h239, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h0, h194, h237, h241, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
                        · rcases h2bigk with h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h0, hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h0, h237, h239, h243, hc23, hc34, hlam, hphi, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h195, hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h215, hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h237, h239, h243, hc02, hc34, hlam, hphi, ht23, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h237, h239, h243, hc23, hc34, hlam, hphi, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h235, hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h237, hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h194, hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h234, hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h239, hlam, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h241, hlam, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h194, h239, hc23, hc34, hlam, hphi, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h0, h239, hc01, hc34, hlam, hphi, ht12, ht23, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            rcases p245_3 (m.d 0 2) (by simp) with h263 | h263
                            · linarith only [h195, h263, hlam]
                            · linarith only [h194, h263, hlam]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [hlam, p245_0]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h194, h215, h239, hc23, hc34, hlam, hphi, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h194, h241, hc23, hc35, hlam, hphi, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h0, h241, hc01, hc35, hlam, hphi, ht12, ht23, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            rcases p245_3 (m.d 0 2) (by simp) with h270 | h270
                            · linarith only [h215, h270, hlam]
                            · linarith only [h194, h270, hlam]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [h243, hlam, p245_1]
                          · have p245_0 := h245c.1
                            have p245_1 := h245c.2.1
                            have p245_2 := h245c.2.2.1
                            have p245_3 := h245c.2.2.2
                            linarith only [hlam, p245_0]
                        · linarith only [h195, h233, h239, h244, hlam]
                      · linarith only [h195, h233, h243, hlam]
            · linarith only [h0, h194, h234, hlam]
          · linarith only [h233, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h279 | h279
      · linarith only [h194, h279, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h281 | h281
        · rcases m.htr 0 4 5 (by decide) (by decide) with h282 | h282
          · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
            · linarith only [h194, h281, h282, h283, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
              · linarith only [h279, h281, h282, h283, h285, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                · rcases m.htr 2 3 4 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h290 | h290
                      · linarith only [h0, h281, h285, h288, h290, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h282, h290, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h281, h282, h285, h288, h289, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h194, h281, h282, h288, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · linarith only [h0, h281, h287, hlam]
          · linarith only [h282, hc45, hlam, hphi, u4ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
          · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
            · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
              · linarith only [h279, h297, h299, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h0, h194, h298, h299, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
              · linarith only [h298, h302, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                · linarith only [h281, h297, h298, h304, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h309 | h309
                        · linarith only [h306, h309, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h297, h309, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h279, h297, h308, hlam]
                    · linarith only [h279, h297, h306, h307, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h298, h306, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h297, hc45, hlam, hphi, u4ehi0]

theorem r1l7_13_25_L_0_H_R (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h1, h12, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h15, h3, h5, h7, h9, hlam]
                          · linarith only [h15, h7, h9, hc23, hlam, hphi, u3elo4]
                        · linarith only [h14, h4, h5, hc23, hlam, hphi, u3elo4]
                    · linarith only [h11, h4, h5, hc13, hlam, hphi, u3elo4]
                · linarith only [h2, h4, h5, h7, h8, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h22, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h1, h25, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h28, h5, hc03, hlam, hphi, u3elo2]
                          · linarith only [h21, h27, h28, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h27, h7, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h21, h24, h4, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h1, h36, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                          · linarith only [h39, h5, hc03, hlam, hphi, u3elo2]
                          · linarith only [h39, h7, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h38, h7, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h35, h4, h5, hc13, hlam, hphi, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
            · linarith only [h4, h44, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
              · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                  · linarith only [h0, h48, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                    · linarith only [h4, h50, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                      · linarith only [h1, h3, h4, h44, h52, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                        · linarith only [h1, h4, h54, hc13, hlam, hphi, u3elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                          · linarith only [h1, h3, h4, h44, h46, h56, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                          · linarith only [h47, h48, h54, h56, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                  · linarith only [h47, h59, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                    · linarith only [h1, h4, h61, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                      · linarith only [h1, h4, h63, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                        · linarith only [h4, h65, hc03, hlam, hphi, u3elo2]
                        · linarith only [h46, h47, h65, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                · rcases m.htr 1 2 5 (by decide) (by decide) with h69 | h69
                  · linarith only [h1, h4, h46, h69, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                    · linarith only [h1, h4, h71, hlam]
                    · linarith only [h46, h68, h71, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                  · linarith only [h1, h4, h46, h74, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                    · linarith only [h1, h4, h76, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                      · linarith only [h1, h44, h78, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                        · linarith only [h4, h80, hc03, hlam, hphi, u3elo2]
                        · linarith only [h46, h80, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h83 | h83
          · rcases m.htr 0 3 5 (by decide) (by decide) with h84 | h84
            · linarith only [h84, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
              · linarith only [h0, h3, h84, h86, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                  · linarith only [h1, h3, h84, h86, h89, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                      · linarith only [h1, h3, h84, h92, hlam]
                      · linarith only [h1, h3, h86, h92, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h83, h84, h86, h88, h91, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                  · linarith only [h86, h96, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                      · linarith only [h1, h3, h84, h99, hlam]
                      · linarith only [h1, h3, h98, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h83, h84, h86, h98, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h103 | h103
            · linarith only [h103, h83, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
              · linarith only [h0, h103, h105, h3, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                  · linarith only [h1, h103, h105, h108, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                    · linarith only [h1, h103, h110, h3, h83, hc03, hlam, hphi, u3elo4]
                    · linarith only [h105, h107, h110, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                  · linarith only [h105, h113, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                    · linarith only [h1, h103, h115, h3, h83, hc03, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
                      · linarith only [h103, h115, h117, h2, h3, hlam]
                      · linarith only [h105, h115, h117, h2, h3, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h120 | h120
        · linarith only [h120, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h122 | h122
          · linarith only [h1, h122, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
            · linarith only [h122, h124, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
              · linarith only [h0, h122, h126, h2, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                · linarith only [h1, h126, h128, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                  · linarith only [h1, h122, h126, h130, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                    · linarith only [h1, h122, h132, h2, hlam]
                    · linarith only [h1, h126, h132, h2, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h136 | h136
    · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
      · rcases m.htr 0 1 5 (by decide) (by decide) with h138 | h138
        · linarith only [h0, h138, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h140 | h140
          · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
            · linarith only [h141, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
              · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                      · linarith only [h136, h138, h141, h147, hlam]
                      · linarith only [h136, h138, h147, hc13, hlam, hphi, u3elo4]
                    · linarith only [h140, h141, h143, h146, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                    · linarith only [h0, h136, h145, h151, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h140, h141, h143, h151, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h137, h144, hlam]
              · linarith only [h0, h143, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
            · linarith only [h140, h156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
              · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                    · linarith only [h0, h136, h140, h161, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h136, h140, h163, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · linarith only [h137, h138, h161, h163, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                    · linarith only [h0, h136, h140, h160, h166, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h168 | h168
                      · linarith only [h136, h140, h156, h168, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · linarith only [h0, h137, h158, h160, h166, h168, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h137, h159, hlam]
              · linarith only [h0, h158, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h173 | h173
        · linarith only [h0, h173, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
          · linarith only [h136, h137, h175, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
            · linarith only [h175, h177, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                    · linarith only [h175, h182, hc03, hlam, hphi, u3elo1]
                    · linarith only [h136, h137, h182, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                    · linarith only [h136, h137, h175, h180, h181, h185, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h136, h137, h179, h185, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h188 | h188
                  · linarith only [h180, h188, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                    · linarith only [h0, h136, h180, h190, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h136, h179, h180, h190, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h136, h179, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h194 | h194
      · rcases m.htr 0 1 5 (by decide) (by decide) with h195 | h195
        · linarith only [h136, h195, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h197 | h197
          · rcases m.htr 0 3 5 (by decide) (by decide) with h198 | h198
            · linarith only [h198, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
              · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                · rcases m.htr 1 2 5 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h136, h198, h204, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h136, h194, h201, h204, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h136, h194, h201, h203, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h209 | h209
                      · linarith only [h209, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                      · linarith only [h136, h194, h201, h209, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h136, h194, h201, h208, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h136, h194, h200, h201, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h200, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h136, h194, h197, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
        · linarith only [h0, h216, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h218 | h218
          · rcases m.htr 0 3 5 (by decide) (by decide) with h219 | h219
            · linarith only [h136, h219, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                      · linarith only [h194, h218, h219, h225, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h136, h225, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h136, h224, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                      · linarith only [h219, h230, hc03, hlam, hphi, u3elo1]
                      · linarith only [h136, h230, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h136, h229, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                  · linarith only [h222, h234, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                    · linarith only [h221, h222, h236, hlam]
                    · linarith only [h218, h219, h236, hc13, hlam, hphi, u3elo4]
              · linarith only [h0, h221, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h240 | h240
            · linarith only [h218, h240, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
              · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 2 5 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h245 | h245
                    · linarith only [h218, h245, hc03, hlam, hphi, u3elo1]
                    · linarith only [h136, h245, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                    · linarith only [h136, h218, h248, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h136, h248, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                  · linarith only [h243, h251, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                    · linarith only [h136, h218, h253, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h136, h253, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h242, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_12_13_15_H_L_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h14, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h17, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
            · linarith only [h20, h3, h4, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h23, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h22, h3, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
            · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                · linarith only [h27, h3, h30, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h1, h30, h32, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h27, h32, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                · linarith only [h3, h35, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
                  · linarith only [h1, h35, h37, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h27, h37, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h27, h28, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h41 | h41
            · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
              · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                · linarith only [h0, h43, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                  · linarith only [h1, h27, h43, h45, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                    · linarith only [h0, h47, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                      · linarith only [h2, h49, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h41, h42, h45, h49, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                · linarith only [h0, h27, h3, h41, h52, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                  · linarith only [h0, h54, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h0, h27, h42, h56, hc25, hlam, hphi, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h2, h27, h42, h58, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                          · linarith only [h0, h27, h42, h61, hc12, hlam, hphi, u2elo3]
                          · linarith only [h0, h27, h61, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h41, h60, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
              · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h3, h66, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h27, h68, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h0, h70, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                      · linarith only [h2, h72, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h65, h72, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                · linarith only [h0, h3, h41, h65, h75, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h0, h27, h77, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                    · linarith only [h0, h3, h41, h65, h79, hc25, hlam, hphi, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                      · linarith only [h0, h2, h3, h41, h65, h81, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · linarith only [h0, h3, h41, h83, hc12, hlam, hphi, u2elo2]
                        · linarith only [h0, h3, h83, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h86 | h86
        · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
          · linarith only [h0, h2, h87, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h89 | h89
            · linarith only [h1, h2, h89, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                · linarith only [h0, h92, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h86, h87, h92, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h2, h91, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
          · linarith only [h0, h2, h96, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
            · linarith only [h1, h2, h98, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                · linarith only [h0, h101, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h1, h101, h103, h2, h96, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h103, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h100, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h108 | h108
    · rcases m.htr 0 1 4 (by decide) (by decide) with h109 | h109
      · rcases m.htr 0 2 3 (by decide) (by decide) with h110 | h110
        · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
          · rcases m.htr 0 3 4 (by decide) (by decide) with h112 | h112
            · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                      · linarith only [h0, h109, h117, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h113, h117, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h108, h114, h116, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h108, h114, h115, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h108, h114, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                      · linarith only [h0, h109, h113, h126, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                        · linarith only [h0, h108, h123, h128, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h108, h112, h128, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h125, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h108, h123, h124, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h123, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
              · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h109, h138, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h109, h134, h138, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h108, h135, h137, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h108, h135, h136, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h135, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
                      · linarith only [h109, h112, h134, h147, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                        · linarith only [h0, h108, h144, h149, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h151 | h151
                          · linarith only [h0, h109, h112, h134, h145, h151, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h153 | h153
                            · linarith only [h108, h112, h134, h144, h153, hc23, hlam, hphi, u3elo3]
                            · linarith only [h112, h153, hc03, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h146, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h108, h144, h145, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h144, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h0, h109, h111, hlam]
        · linarith only [h0, h108, h110, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h161 | h161
        · rcases m.htr 0 2 4 (by decide) (by decide) with h162 | h162
          · rcases m.htr 0 3 4 (by decide) (by decide) with h163 | h163
            · linarith only [h108, h109, h163, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                        · linarith only [h108, h163, h166, h170, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                          · linarith only [h162, h172, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h162, h165, h172, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h109, h162, h165, h169, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h108, h109, h166, h167, h168, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h108, h166, h167, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h166, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h108, h109, h165, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h180 | h180
            · linarith only [h0, h108, h162, h180, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h182 | h182
              · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
                  · linarith only [h0, h108, h162, h183, h184, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h108, h183, h184, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h183, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h0, h108, h162, h182, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h0, h108, h161, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h190 | h190
      · rcases m.htr 0 2 3 (by decide) (by decide) with h191 | h191
        · rcases m.htr 0 2 4 (by decide) (by decide) with h192 | h192
          · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
            · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
              · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                      · linarith only [h108, h190, h198, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h108, h190, h194, h196, h198, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h108, h195, h197, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h108, h190, h194, h195, h196, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h191, h195, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h207 | h207
                      · linarith only [h108, h190, h194, h204, h207, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                        · linarith only [h191, h209, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h193, h209, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h190, h205, h206, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h108, h204, h205, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h190, h204, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h108, h190, h193, hlam]
          · linarith only [h108, h190, h191, h192, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h217 | h217
          · rcases m.htr 0 3 4 (by decide) (by decide) with h218 | h218
            · rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
              · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                · linarith only [h0, h191, h220, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h190, h219, h220, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                · linarith only [h0, h191, h223, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h190, h223, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h0, h190, h191, h218, hlam]
          · linarith only [h0, h190, h217, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h228 | h228
        · rcases m.htr 0 2 4 (by decide) (by decide) with h229 | h229
          · rcases m.htr 0 3 4 (by decide) (by decide) with h230 | h230
            · rcases m.htr 0 4 5 (by decide) (by decide) with h231 | h231
              · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h235 | h235
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                        · linarith only [h228, h236, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h228, h230, h236, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h190, h231, h235, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h234, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h229, h233, hlam]
                · linarith only [h0, h232, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                      · linarith only [h190, h231, h244, h246, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h190, h246, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h245, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h108, h229, h243, h244, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h243, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
              · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
                · rcases m.htr 1 2 4 (by decide) (by decide) with h254 | h254
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h256 | h256
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h257 | h257
                        · linarith only [h228, h230, h257, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h259 | h259
                          · linarith only [h229, h259, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h252, h257, h259, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h190, h229, h252, h256, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h255, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h254, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h253, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                      · linarith only [h108, h230, h252, h267, h269, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h190, h269, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h268, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h229, h267, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h228, h266, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h275 | h275
            · linarith only [h228, h229, h275, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h277 | h277
              · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
                · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
                  · linarith only [h229, h279, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h279, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h228, h278, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h228, h229, h277, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
          · rcases m.htr 0 3 4 (by decide) (by decide) with h285 | h285
            · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
              · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                · linarith only [h228, h284, h287, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h287, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
                · linarith only [h228, h284, h290, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h290, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h228, h284, h285, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h294 | h294
            · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
              · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                · linarith only [h228, h296, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h296, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                · linarith only [h0, h228, h299, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h299, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h302 | h302
              · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                · linarith only [h0, h228, h303, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h303, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
                · linarith only [h0, h228, h306, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h306, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_15_H_L_L_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h2, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h14, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h17, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · linarith only [h2, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 0 3 4 (by decide) (by decide) with h22 | h22
            · linarith only [h2, h22, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h25, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h2, h25, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h2, h24, h3, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h2, h21, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
        · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
            · rcases m.htr 0 4 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h34, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                  · linarith only [h1, h36, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h32, h36, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                · linarith only [h0, h2, h30, h39, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h1, h41, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h32, h41, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h2, h30, h32, hlam]
          · linarith only [h30, h31, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h46 | h46
          · rcases m.htr 0 3 4 (by decide) (by decide) with h47 | h47
            · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
              · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                · linarith only [h0, h2, h49, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                  · linarith only [h1, h51, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h47, h51, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h30, h46, h48, hc25, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
              · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
                · linarith only [h0, h2, h46, h56, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                  · linarith only [h47, h58, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                    · linarith only [h2, h46, h47, h60, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h2, h46, h60, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h2, h46, h47, h55, hc25, hlam, hphi, u5elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h64 | h64
            · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
              · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h2, h66, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                  · linarith only [h1, h68, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h64, h68, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                · linarith only [h0, h2, h64, h71, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                  · linarith only [h1, h73, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h64, h73, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
              · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                · linarith only [h0, h2, h77, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                  · linarith only [h1, h79, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                    · linarith only [h0, h2, h64, h81, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h0, h2, h81, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                · linarith only [h0, h2, h84, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                  · linarith only [h1, h86, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                    · linarith only [h64, h88, hc03, hlam, hphi, u3elo2]
                    · linarith only [h0, h2, h88, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h92 | h92
    · rcases m.htr 0 2 3 (by decide) (by decide) with h93 | h93
      · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
        · rcases m.htr 0 2 5 (by decide) (by decide) with h95 | h95
          · rcases m.htr 0 3 4 (by decide) (by decide) with h96 | h96
            · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
              · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                  · linarith only [h92, h99, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h92, h96, h99, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h98, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h92, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h104, h96, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h103, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
              · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                  · linarith only [h110, h92, h96, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                    · linarith only [h109, h112, h92, h96, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                      · linarith only [h0, h109, h114, h92, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h116, h94, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h108, h116, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h109, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
                · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                  · linarith only [h121, h92, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                    · linarith only [h123, h96, hc03, hlam, hphi, u3elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                      · linarith only [h0, h120, h125, h92, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h108, h127, h94, h96, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                          · linarith only [h108, h120, h129, h92, h96, hc23, hlam, hphi, u3elo3]
                          · linarith only [h120, h129, h92, h96, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h120, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h93, h95, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h134 | h134
          · rcases m.htr 0 3 4 (by decide) (by decide) with h135 | h135
            · linarith only [h0, h135, h92, h94, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
              · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
                  · linarith only [h135, h139, h92, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                    · linarith only [h0, h135, h138, h141, h92, h94, hlam]
                    · linarith only [h0, h141, h92, h94, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h138, h92, hc13, hlam, hphi, u3elo2]
              · linarith only [h0, h137, h92, h94, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h134, h92, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h92, h93, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h148 | h148
      · rcases m.htr 0 2 4 (by decide) (by decide) with h149 | h149
        · rcases m.htr 0 2 5 (by decide) (by decide) with h150 | h150
          · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
            · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
              · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                    · linarith only [h148, h155, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h151, h155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h148, h151, h154, h92, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h153, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                    · linarith only [h148, h162, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h148, h151, h162, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h148, h151, h161, h92, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h160, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
              · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                  · linarith only [h151, h169, hc03, hlam, hphi, u3elo1]
                  · linarith only [h169, h92, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h148, h168, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                  · linarith only [h151, h174, h92, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h174, h92, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h148, h149, h173, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · linarith only [h148, h150, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h179 | h179
          · rcases m.htr 0 3 4 (by decide) (by decide) with h180 | h180
            · linarith only [h148, h149, h180, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h182 | h182
              · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                  · linarith only [h180, h184, hc03, hlam, hphi, u3elo1]
                  · linarith only [h184, h92, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h148, h183, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h149, h179, h182, hc25, hlam, hphi, u5elo4]
          · linarith only [h148, h179, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h190 | h190
        · rcases m.htr 0 2 5 (by decide) (by decide) with h191 | h191
          · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
            · rcases m.htr 0 4 5 (by decide) (by decide) with h193 | h193
              · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h198 | h198
                        · linarith only [h190, h198, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h148, h190, h193, h194, h198, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h148, h197, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h148, h190, h193, h196, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h192, h195, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h194, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
                · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                        · linarith only [h190, h193, h209, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                          · linarith only [h190, h193, h207, h211, hlam]
                          · rcases h2bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, hlam, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h148, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h148, h205, h207, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p213_1, u3elo1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h148, h205, h207, h209, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p213_1, u3elo1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h219 | h219
                              · linarith only [h0, h219, hlam]
                              · rcases p213_3 (m.d 1 2) (by simp) with h221 | h221
                                · rcases p213_3 (m.d 2 3) (by simp) with h222 | h222
                                  · linarith only [h205, h222, hlam]
                                  · linarith only [h148, h222, hlam]
                                · linarith only [h0, h221, hlam]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h0, h148, hc01, hc12, hlam, hphi, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h148, h191, h205, h209, hlam, p213_2]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h148, h191, h205, hlam, p213_2]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h191, h205, h207, h209, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h205, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h233 | h233
                              · linarith only [h148, h233, hlam]
                              · linarith only [h190, h233, hlam]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              rcases p213_3 (m.d 0 2) (by simp) with h236 | h236
                              · linarith only [h148, h236, hlam]
                              · linarith only [h191, h236, hlam]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h190, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h191, h209, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p213_1, u0elo1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h207, hlam, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h209, hlam, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h191, hlam, p213_0]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h148, h191, h205, hlam, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h208, hlam, p213_1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [h148, h191, h205, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p213_1, u3elo1]
                            · have p213_0 := h213c.1
                              have p213_1 := h213c.2.1
                              have p213_2 := h213c.2.2.1
                              have p213_3 := h213c.2.2.2
                              linarith only [hlam, p213_0]
                      · linarith only [h148, h208, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h148, h190, h207, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h192, h193, h206, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h205, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h148, h190, h192, hlam]
          · linarith only [h190, h191, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h255 | h255
          · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
            · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
              · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h261 | h261
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h263 | h263
                          · linarith only [h256, h263, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h257, h263, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h190, h255, h256, h257, h261, h262, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h148, h261, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h148, h255, h260, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h256, h259, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h258, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h190, h255, h257, hc25, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h272 | h272
              · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
                · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
                  · linarith only [h256, h274, hc03, hlam, hphi, u3elo1]
                  · linarith only [h274, h92, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h273, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h148, h255, h256, h272, hc25, hlam, hphi, u5elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h279 | h279
            · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
                · rcases m.htr 1 3 4 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h286 | h286
                          · linarith only [h279, h286, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h280, h286, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h280, h285, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h148, h284, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h148, h283, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h279, h282, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h281, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                        · linarith only [h0, h190, h280, h294, h296, h298, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h0, h190, h298, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h148, h297, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h148, h279, h296, hlam]
                  · linarith only [h279, h295, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h294, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h305 | h305
              · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
                · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                  · linarith only [h279, h307, hc03, hlam, hphi, u3elo1]
                  · linarith only [h307, h92, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h306, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
                  · linarith only [h0, h148, h279, h312, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h312, h92, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h311, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
