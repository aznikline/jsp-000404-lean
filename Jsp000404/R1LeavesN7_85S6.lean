import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LR_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h6, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h7, h8, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h12, h7, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h12, h5, h8, hc23, hlam, hphi, ht34, u4elo0]
                · linarith only [h0, h3, h6, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h16, h2, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h0, h18, h2, h21, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h21, h5, hc34, hlam, hphi, u4elo0]
                      · linarith only [h16, h20, h5, hc12, hlam, hphi, ht23, ht34, u4elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h18, h19, h25, hlam]
                      · linarith only [h16, h25, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h18, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
            · linarith only [h3, h30, h4, hlam]
            · linarith only [h30, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h2, h3, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h34 | h34
        · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
          · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
            · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
              · linarith only [h2, h34, h36, h37, hc12, hlam, hphi, ht01, u0ehi9]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h0, h39, h42, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h36, h40, h42, hc34, hlam, hphi, u4elo0]
                    · linarith only [h2, h41, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h2, h34, h36, h40, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h2, h34, h39, hc12, hc23, hlam, hphi]
            · linarith only [h36, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
            · linarith only [h34, h35, h49, hlam]
            · linarith only [h49, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h34, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h54 | h54
    · rcases m.htr 0 2 3 (by decide) (by decide) with h55 | h55
      · rcases m.htr 0 2 4 (by decide) (by decide) with h56 | h56
        · rcases m.htr 0 2 5 (by decide) (by decide) with h57 | h57
          · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
            · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
              · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                        · linarith only [h55, h61, h64, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h58, h64, hc34, hlam, hphi, u4elo0]
                      · linarith only [h58, h63, hc24, hlam, hphi, u4elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                      · linarith only [h61, h62, h68, hlam]
                      · linarith only [h58, h68, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
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
                            linarith only [h0, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h71, h73, hc45, hlam, hphi, ht0b, ht5b, p74_1, u0elo1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h61, h71, h73, hc45, hlam, hphi, ht0b, ht5b, p74_1, u0elo1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h79 | h79
                            · rcases p74_3 (m.d 1 2) (by simp) with h80 | h80
                              · rcases p74_3 (m.d 2 3) (by simp) with h81 | h81
                                · linarith only [h55, h81, hlam]
                                · linarith only [h71, h81, hlam]
                              · linarith only [h0, h80, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p74_1, u0elo1]
                            · linarith only [h79, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p74_1, u0ehi6]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h88 | h88
                            · linarith only [h0, h88, hlam]
                            · linarith only [h55, h88, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h91 | h91
                            · linarith only [h0, h91, hlam]
                            · linarith only [h56, h91, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h94 | h94
                            · linarith only [h0, h94, hlam]
                            · linarith only [h57, h94, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h55, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h59, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h61, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h61, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p74_1, u4elo3]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h56, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h60, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, h54, h60, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p74_1, u0elo1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, h54, h60, h71, h73, hc45, hlam, hphi, ht0b, ht5b, p74_1, u0elo1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h57, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h71, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h72, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                        · linarith only [h61, h73, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h58, h61, h71, h72, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                        · rcases h2bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h0, hlam, p116_1]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            rcases p116_3 (m.d 0 2) (by simp) with h119 | h119
                            · rcases p116_3 (m.d 1 2) (by simp) with h120 | h120
                              · rcases p116_3 (m.d 2 3) (by simp) with h121 | h121
                                · linarith only [h121, hlam, p116_0]
                                · rcases p116_3 (m.d 2 4) (by simp) with h123 | h123
                                  · linarith only [h123, h56, hlam]
                                  · linarith only [h123, h61, hlam]
                              · linarith only [h120, h59, hlam]
                            · linarith only [h119, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h114, hc45, hlam, hphi, ht0b, ht5b, p116_1, u0elo1]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            rcases p116_3 (m.d 0 2) (by simp) with h129 | h129
                            · rcases p116_3 (m.d 1 2) (by simp) with h130 | h130
                              · rcases p116_3 (m.d 2 3) (by simp) with h131 | h131
                                · linarith only [h131, h55, hlam]
                                · rcases p116_3 (m.d 2 4) (by simp) with h133 | h133
                                  · linarith only [h133, h56, hlam]
                                  · linarith only [h114, h133, hlam]
                              · linarith only [h0, h114, h130, h54, h60, hc45, hlam, hphi, ht0b, ht5b, p116_1, u0elo1]
                            · linarith only [h129, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p116_1, u0ehi6]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            rcases p116_3 (m.d 0 2) (by simp) with h140 | h140
                            · linarith only [h0, h140, hlam]
                            · linarith only [h140, h55, hlam]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            rcases p116_3 (m.d 0 2) (by simp) with h143 | h143
                            · linarith only [h0, h143, hlam]
                            · linarith only [h143, h56, hlam]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            rcases p116_3 (m.d 0 2) (by simp) with h146 | h146
                            · linarith only [h0, h146, hlam]
                            · linarith only [h146, h57, hlam]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h55, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h59, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h61, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h71, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h56, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h60, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h54, h60, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u0elo0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h0, h54, h60, h71, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u0elo1]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h57, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p116_1]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h57, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u0elo1]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [h114, hlam, p116_0]
                          · have p116_0 := h116c.1
                            have p116_1 := h116c.2.1
                            have p116_2 := h116c.2.2.1
                            have p116_3 := h116c.2.2.2
                            linarith only [hlam, p116_0]
                        · linarith only [h115, h61, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h114, h58, hc24, hlam, hphi, u4elo0]
                · linarith only [h0, h60, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h54, h58, h59, hc23, hlam, hphi, ht01, ht12, u0ehi9]
            · linarith only [h58, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
            · linarith only [h0, h169, h54, h57, hlam]
            · linarith only [h169, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h0, h54, h56, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h173 | h173
        · rcases m.htr 0 2 5 (by decide) (by decide) with h174 | h174
          · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
            · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
              · linarith only [h0, h175, h176, h54, h55, hc12, hlam, hphi, ht01, u0ehi9]
              · linarith only [h0, h175, h176, h54, hc23, hlam, hphi, ht01, ht12, u0ehi9]
            · linarith only [h175, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h180 | h180
            · linarith only [h0, h174, h180, h54, hlam]
            · linarith only [h180, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h0, h173, h54, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo2]
    · linarith only [h54, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo1]

theorem r1l7_20_13_14_M_IR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h10, h13, h16, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h16, h9, hc34, hlam, hphi, u4elo0]
                                · linarith only [h15, h9, hc24, hlam, hphi, u4elo0]
                              · linarith only [h14, h8, hc23, hlam, hphi, u3elo0]
                            · linarith only [h13, h7, hc23, hlam, hphi, u3elo0]
                          · linarith only [h10, h12, h6, h9, hc23, hlam, hphi, ht34, u4elo0]
                        · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                · linarith only [h10, h24, h28, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                                · linarith only [h26, h28, h9, hc34, hlam, hphi, u4elo0]
                              · linarith only [h10, h24, h26, h27, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · linarith only [h10, h24, h26, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h24, h25, h6, h9, hc24, hlam, hphi, u4elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                                  · rcases h0bigk with h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hc01, hlam, hphi, p39_1, u0ehi1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hc01, hlam, hphi, p39_1, u0ehi2]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h24, h34, h36, h38, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p39_1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hc01, hlam, hphi, p39_1, u0ehi4]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h0, hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hc02, hlam, hphi, p39_1, u0ehi2]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h0, h24, h34, h36, h38, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p39_1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p39_1, u0ehi4]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h1, hlam, p39_1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h4, hlam, p39_1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h24, h34, h36, h38, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p39_1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht12, ht23, p39_1, u0ehi4, u3elo0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h2, hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h5, hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h7, hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p39_1, u0ehi4, u4elo0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h3, hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h6, hlam, p39_1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h8, hlam, p39_0]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [h9, hlam, p39_1]
                                    · have p39_0 := h39c.1
                                      have p39_1 := h39c.2.1
                                      have p39_2 := h39c.2.2.1
                                      have p39_3 := h39c.2.2.2
                                      linarith only [hlam, p39_0]
                                  · linarith only [h38, h9, hc34, hlam, hphi, u4elo0]
                                · linarith only [h24, h37, h9, hc12, hlam, hphi, ht23, ht34, u4elo0]
                              · linarith only [h36, h8, hc23, hlam, hphi, u3elo0]
                            · linarith only [h10, h34, h35, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                                  · rcases h0bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc01, hlam, hphi, p73_1, u0ehi1]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc01, hlam, hphi, p73_1, u0ehi2]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc01, hlam, hphi, p73_1, u0ehi3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc01, hlam, hphi, p73_1, u0ehi4]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h0, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc02, hlam, hphi, p73_1, u0ehi2]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p73_1, u0ehi3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p73_1, u0ehi4]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h1, hlam, p73_1]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h4, hlam, p73_1]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc03, hlam, hphi, p73_1, u0ehi3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht12, ht23, p73_1, u0ehi4, u3elo0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h2, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h5, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h7, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc04, hlam, hphi, p73_1, u0ehi4]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h3, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h6, hlam, p73_1]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h8, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h9, hlam, p73_1]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                  · linarith only [h72, h9, hc34, hlam, hphi, u4elo0]
                                · linarith only [h71, h9, hc24, hlam, hphi, u4elo0]
                              · linarith only [h70, h8, hc23, hlam, hphi, u3elo0]
                            · linarith only [h10, h69, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h9, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
                  · linarith only [h8, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
                · linarith only [h7, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
                · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
                  · linarith only [h107, h4, h6, hlam]
                  · linarith only [h107, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
                · linarith only [h106, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h113 | h113
          · rcases m.htr 0 2 4 (by decide) (by decide) with h114 | h114
            · rcases m.htr 0 2 5 (by decide) (by decide) with h115 | h115
              · linarith only [h0, h115, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h117 | h117
                · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
                  · linarith only [h1, h118, h3, hlam]
                  · linarith only [h118, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
                · linarith only [h117, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
            · linarith only [h113, h114, hc23, hlam, hphi, ht34, u4elo2]
          · linarith only [h113, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
    · linarith only [h0, h1, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h126 | h126
    · rcases m.htr 0 1 4 (by decide) (by decide) with h127 | h127
      · rcases m.htr 0 1 5 (by decide) (by decide) with h128 | h128
        · rcases m.htr 0 2 3 (by decide) (by decide) with h129 | h129
          · rcases m.htr 0 2 4 (by decide) (by decide) with h130 | h130
            · rcases m.htr 0 2 5 (by decide) (by decide) with h131 | h131
              · rcases m.htr 0 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                                  · linarith only [h0, h126, h135, h138, h141, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h134, h141, hc34, hlam, hphi, u4elo0]
                                · linarith only [h134, h140, hc24, hlam, hphi, u4elo0]
                              · linarith only [h133, h139, hc23, hlam, hphi, u3elo0]
                            · linarith only [h132, h138, hc23, hlam, hphi, u3elo0]
                          · linarith only [h0, h137, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                        · linarith only [h0, h136, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h0, h135, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h134, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
                  · linarith only [h132, h133, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
                · linarith only [h132, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
              · linarith only [h0, h128, h131, hlam]
            · linarith only [h0, h126, h130, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h126, h129, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h156 | h156
          · rcases m.htr 0 2 4 (by decide) (by decide) with h157 | h157
            · rcases m.htr 0 2 5 (by decide) (by decide) with h158 | h158
              · rcases m.htr 0 3 4 (by decide) (by decide) with h159 | h159
                · rcases m.htr 0 3 5 (by decide) (by decide) with h160 | h160
                  · linarith only [h126, h128, h160, hlam]
                  · linarith only [h159, h160, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
                · linarith only [h159, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h164 | h164
                · rcases m.htr 0 3 5 (by decide) (by decide) with h165 | h165
                  · linarith only [h0, h126, h158, h165, hlam]
                  · linarith only [h164, h165, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
                · linarith only [h164, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
            · linarith only [h0, h126, h157, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h126, h156, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
      · linarith only [h126, h127, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2, u4elo1]
    · linarith only [h126, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_20_13_14_M_IR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h8, hlam, hphi, ht34, u3ehi2, u4elo3]
                · linarith only [h6, h7, hlam, hphi, ht34, u3ehi1, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h12, h13, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h13, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                    · rcases h0bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hlam, p18_0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h16, h17, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p18_1, u3ehi4]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hc01, hlam, hphi, p18_1, u0ehi2]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hc01, hlam, hphi, p18_1, u0ehi3]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hc01, hlam, hphi, p18_1, u0ehi4]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h0, hlam, p18_0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hlam, p18_0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h16, h17, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p18_1, u3ehi4]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h0, h5, hc01, hlam, hphi, p18_1, u0ehi4]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, p18_1, u0ehi4]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h1, hlam, p18_1]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h3, hlam, p18_1]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hlam, p18_0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h5, hc03, hlam, hphi, p18_1, u0ehi4]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, p18_1, u0ehi4]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h2, hlam, p18_0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h4, hlam, p18_0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hc04, hlam, hphi, p18_1, u0ehi2]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hlam, p18_0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p18_1, u0ehi4, u4elo0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hc05, hlam, hphi, p18_1, u0ehi0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h16, h17, h3, h5, hlam, hphi, ht34, p18_1, u3ehi4, u4elo0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h16, h17, h3, h5, hlam, hphi, ht34, p18_1, u3ehi4, u4elo0]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [h5, hlam, p18_1]
                      · have p18_0 := h18c.1
                        have p18_1 := h18c.2.1
                        have p18_2 := h18c.2.2.1
                        have p18_3 := h18c.2.2.2
                        linarith only [hlam, p18_0]
                    · linarith only [h17, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h16, hlam, hphi, ht34, u3ehi2, u4elo3]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h3, h4, hlam, hphi, ht34, u3ehi2, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h48 | h48
          · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
            · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
              · linarith only [h3, h50, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                    · rcases h0bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hlam, p55_0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h0, h52, h53, h54, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1, u3ehi4]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hc01, hlam, hphi, p55_1, u0ehi2]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h49, hc01, hlam, hphi, p55_1, u0ehi4]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hc01, hlam, hphi, p55_1, u0ehi4]
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
                        linarith only [h3, hlam, p55_0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h49, hc02, hlam, hphi, p55_1, u0ehi4]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h3, hc23, hlam, hphi, ht01, ht12, p55_1, u0ehi4]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h1, hlam, p55_1]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hc03, hlam, hphi, p55_1, u0ehi1]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hlam, p55_0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h3, h49, hc23, hlam, hphi, ht01, ht12, p55_1, u0ehi4]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h3, hc23, hlam, hphi, ht01, ht12, p55_1, u0ehi4]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h2, hlam, p55_0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h48, hlam, p55_0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hc04, hlam, hphi, p55_1, u0ehi2]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hlam, p55_0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p55_1, u0ehi4, u4elo0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h1, h50, h52, h53, h54, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1, u3ehi4]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h0, h49, h52, h53, h54, hlam, hphi, ht34, p55_1, u3ehi4, u4elo0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h1, h49, h50, h52, h53, h54, hlam, hphi, ht34, p55_1, u3ehi4, u4elo0]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [h49, hlam, p55_1]
                      · have p55_0 := h55c.1
                        have p55_1 := h55c.2.1
                        have p55_2 := h55c.2.2.1
                        have p55_3 := h55c.2.2.2
                        linarith only [hlam, p55_0]
                    · linarith only [h54, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h3, h53, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h3, h48, h52, hc12, hc23, hlam, hphi]
            · linarith only [h49, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h48, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · linarith only [h1, h2, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h87 | h87
      · rcases m.htr 0 2 3 (by decide) (by decide) with h88 | h88
        · linarith only [h0, h1, h88, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h90 | h90
          · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
            · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
              · linarith only [h88, h92, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                  · linarith only [h0, h1, h92, h94, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1, h92, h95, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h90, h92, h94, hc12, hc23, hlam, hphi]
            · linarith only [h91, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h90, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · linarith only [h0, h87, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h102 | h102
    · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
      · rcases m.htr 0 2 3 (by decide) (by decide) with h104 | h104
        · rcases m.htr 0 2 4 (by decide) (by decide) with h105 | h105
          · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
              · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                  · linarith only [h0, h102, h107, h109, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h109, hlam, hphi, ht34, u3ehi2, u4elo3]
                · linarith only [h0, h102, h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h102, h107, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h106, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h104, h105, hlam, hphi, ht34, u3ehi2, u4elo2]
        · linarith only [h0, h102, h104, hlam]
      · linarith only [h102, h103, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h118 | h118
      · rcases m.htr 0 2 3 (by decide) (by decide) with h119 | h119
        · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
          · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                    · rcases h0bigk with h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c | h126c
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [hlam, p126_0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h0, hlam, p126_1]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h102, hlam, p126_0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h102, h121, h122, hc12, hlam, hphi, ht01, p126_1, u0ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h102, h122, hc12, hlam, hphi, ht01, p126_1, u0ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h0, h118, h123, h124, h125, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p126_1]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [hlam, p126_0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h0, h102, h118, h123, h124, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p126_1, u3ehi3]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h0, h121, hc12, hlam, hphi, ht01, p126_1, u0ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht01, p126_1, u0ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h118, h123, h124, h125, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p126_1, u3ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h119, hlam, p126_1]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [hlam, p126_0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h102, h121, h122, hc12, hlam, hphi, ht01, p126_1, u0ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h102, h122, hc12, hlam, hphi, ht01, p126_1, u0ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h118, hlam, p126_0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h120, hlam, p126_0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [hc04, hlam, hphi, p126_1, u0ehi2]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [hlam, p126_0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p126_1, u0ehi4, u4elo0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h118, h123, h124, h125, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p126_1, u3ehi4]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h121, hc02, hlam, hphi, ht23, ht34, p126_1, u4elo0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h102, h118, h121, h123, h124, h125, hlam, hphi, ht34, p126_1, u3ehi4, u4elo0]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [h121, hlam, p126_1]
                      · have p126_0 := h126c.1
                        have p126_1 := h126c.2.1
                        have p126_2 := h126c.2.2.1
                        have p126_3 := h126c.2.2.2
                        linarith only [hlam, p126_0]
                    · linarith only [h125, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h124, hlam, hphi, ht34, u3ehi2, u4elo3]
                · linarith only [h102, h122, h123, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h118, h121, h122, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h121, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h119, h120, hlam, hphi, ht34, u3ehi2, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h158 | h158
          · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
            · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
              · linarith only [h119, h160, hc12, hlam, hphi, ht01, u0ehi1]
              · linarith only [h0, h118, h159, h160, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h159, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h0, h118, h158, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo2]
      · linarith only [h118, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]

theorem r1l7_20_14_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h2, h4, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h9, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                · linarith only [h0, h11, h2, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h11, h2, h4, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h14 | h14
          · linarith only [h1, h14, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
            · linarith only [h1, h16, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
              · linarith only [h18, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h18, h2, h20, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h14, h22, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                    · linarith only [h1, h16, h24, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h0, h18, h2, h24, h26, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h2, h20, h26, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
      · linarith only [h29, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h31 | h31
        · linarith only [h0, h1, h31, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h33 | h33
          · linarith only [h0, h33, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
              · linarith only [h37, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                · linarith only [h0, h1, h31, h35, h37, h39, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h0, h33, h41, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                    · linarith only [h0, h1, h35, h39, h43, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h43, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h46 | h46
    · rcases m.htr 0 1 4 (by decide) (by decide) with h47 | h47
      · linarith only [h47, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 2 4 (by decide) (by decide) with h50 | h50
          · linarith only [h50, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
            · linarith only [h0, h46, h50, h52, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h54 | h54
              · linarith only [h54, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
                · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h46, h50, h52, h54, h58, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · linarith only [h0, h46, h50, h54, h58, h60, hc13, hc34, hlam, hphi]
                      · linarith only [h46, h47, h56, h60, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                    · linarith only [h0, h46, h50, h54, h63, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h46, h50, h54, h56, h63, h65, hc23, hc34, hlam, hphi]
                      · linarith only [h46, h47, h56, h65, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h49, h50, h54, h56, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h46, h49, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h70 | h70
      · linarith only [h70, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h72 | h72
        · rcases m.htr 0 2 4 (by decide) (by decide) with h73 | h73
          · linarith only [h73, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
            · linarith only [h72, h73, h75, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
              · linarith only [h77, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · linarith only [h46, h72, h73, h75, h77, h79, h81, h82, h83, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h72, h73, h77, h83, h85, hc23, hc34, hlam, hphi]
                          · linarith only [h72, h73, h79, h81, h82, h85, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h72, h73, h80, h82, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                      · linarith only [h72, h73, h77, h81, h89, hc23, hc34, hlam, hphi]
                      · linarith only [h72, h73, h80, h89, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                    · linarith only [h46, h75, h79, h80, h92, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                      · linarith only [h72, h73, h77, h92, h94, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                        · linarith only [h72, h96, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                          · linarith only [h0, h80, h94, h96, h98, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h72, h73, h98, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h72, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h102 | h102
          · linarith only [h102, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h104 | h104
            · linarith only [h104, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
              · linarith only [h106, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                        · linarith only [h0, h104, h108, h112, h72, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h108, h110, h112, h72, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                        · linarith only [h0, h104, h108, h115, h72, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h110, h111, h115, h72, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                        · linarith only [h110, h119, h46, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h106, h109, h121, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h102, h118, h121, hc01, hc14, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                        · linarith only [h0, h104, h108, h124, h72, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                          · linarith only [h0, h108, h110, h118, h126, h72, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h128 | h128
                            · linarith only [h0, h108, h110, h118, h128, h72, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h108, h110, h128, h72, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h108, h109, h72, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h102, h108, h132, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h106, h134, h138, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · linarith only [h0, h104, h135, h138, h72, hc01, hc14, hlam, hphi]
                          · linarith only [h132, h135, h137, hlam]
                        · linarith only [h0, h108, h136, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                          · linarith only [h135, h144, h70, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h132, h144, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h134, h143, h72, hc01, hc13, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                        · linarith only [h134, h149, h46, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h108, h149, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                        · linarith only [h0, h108, h134, h152, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h108, h152, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_21_14_H_L_L_I (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · linarith only [h1, h6, h8, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h3, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                · linarith only [h1, h11, h13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h13, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
              · linarith only [h0, h17, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                · linarith only [h1, h17, h19, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h19, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
              · linarith only [h0, h22, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                · linarith only [h1, h22, h24, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h24, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h29, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                · linarith only [h1, h29, h3, h31, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h1, h33, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h27, h33, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h36, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                · linarith only [h0, h3, h38, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                  · linarith only [h1, h40, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h27, h36, h40, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
              · linarith only [h0, h44, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h3, h46, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                  · linarith only [h1, h27, h48, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                    · linarith only [h2, h50, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h2, h43, h44, h48, h50, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h53, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h3, h55, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                  · linarith only [h1, h27, h57, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h2, h43, h59, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                          · linarith only [h2, h43, h53, h57, h61, h63, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h27, h53, h62, h63, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                          · linarith only [h0, h3, h62, h66, hc12, hc34, hlam, hphi, ht23]
                          · rcases h4bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h2, h53, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p68_1, u1elo0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h3, hlam, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h27, hlam, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h43, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h2, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h55, hlam, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h57, hlam, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h59, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h62, hc04, hc45, hlam, hphi, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h53, h57, h62, hc12, hc45, hlam, hphi, ht23, ht34, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h1, h27, h53, h62, hc12, hc45, hlam, hphi, ht23, ht34, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h62, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h2, h53, h57, h61, hc12, hc23, hlam, hphi, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h53, h57, h61, hc12, hc23, hlam, hphi, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h61, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h66, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              rcases p68_3 (m.d 0 4) (by simp) with h89 | h89
                              · linarith only [h89, hlam, p68_0]
                              · rcases p68_3 (m.d 1 4) (by simp) with h91 | h91
                                · linarith only [h59, h91, hlam]
                                · rcases p68_3 (m.d 2 4) (by simp) with h93 | h93
                                  · linarith only [h62, h93, hlam]
                                  · linarith only [h3, h93, hlam]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              rcases p68_3 (m.d 0 4) (by simp) with h96 | h96
                              · linarith only [h43, h96, hlam]
                              · linarith only [h2, h96, hlam]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h0, h3, hc12, hc45, hlam, hphi, ht23, ht34, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h1, h27, h53, hc12, hc45, hlam, hphi, ht23, ht34, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                          · rcases h4bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h102, h43, h53, h57, hc12, hc24, hlam, hphi, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h3, hlam, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h27, hlam, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h43, hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h2, hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h55, hlam, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h57, hlam, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h59, hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              rcases p104_3 (m.d 0 4) (by simp) with h115 | h115
                              · linarith only [h115, h3, hlam]
                              · rcases p104_3 (m.d 1 4) (by simp) with h117 | h117
                                · linarith only [h117, h55, hlam]
                                · rcases p104_3 (m.d 2 4) (by simp) with h119 | h119
                                  · rcases p104_3 (m.d 3 4) (by simp) with h120 | h120
                                    · rcases p104_3 (m.d 4 5) (by simp) with h121 | h121
                                      · linarith only [h102, h121, hlam]
                                      · linarith only [h121, h43, hlam]
                                    · linarith only [h120, h27, hlam]
                                  · linarith only [h119, h3, hlam]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              rcases p104_3 (m.d 0 4) (by simp) with h126 | h126
                              · linarith only [h126, h3, hlam]
                              · linarith only [h126, h2, hlam]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h61, hlam, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h2, h43, h53, h57, h61, hc12, hc34, hlam, hphi, ht23, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              rcases p104_3 (m.d 0 4) (by simp) with h132 | h132
                              · linarith only [h132, h27, hlam]
                              · rcases p104_3 (m.d 1 4) (by simp) with h134 | h134
                                · linarith only [h134, h57, hlam]
                                · rcases p104_3 (m.d 2 4) (by simp) with h136 | h136
                                  · linarith only [h136, h61, hlam]
                                  · linarith only [h136, h3, hlam]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              rcases p104_3 (m.d 0 4) (by simp) with h139 | h139
                              · linarith only [h139, h27, hlam]
                              · linarith only [h139, h2, hlam]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h2, h43, h53, h57, hc12, hc34, hlam, hphi, ht23, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h102, h2, h53, h57, hc12, hc24, hlam, hphi, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h102, h53, h57, hc12, hc24, hlam, hphi, p104_1]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h102, hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [h103, hlam, p104_0]
                            · have p104_0 := h104c.1
                              have p104_1 := h104c.2.1
                              have p104_2 := h104c.2.2.1
                              have p104_3 := h104c.2.2.2
                              linarith only [hlam, p104_0]
                          · linarith only [h102, h103, h61, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                          · linarith only [h0, h102, h151, h3, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h151, h53, h61, hc12, hc45, hlam, hphi, ht23, ht34]
      · linarith only [h2, hc01, hlam, hphi, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

end R2N4
