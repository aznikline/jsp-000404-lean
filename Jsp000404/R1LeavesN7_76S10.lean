import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_15_M_LI_L_R (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h11, h2, h8, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h11, h13, h8, h9, hlam]
                        · linarith only [h13, h3, h6, h7, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h1, h18, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h18, h20, h3, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h20, h3, h6, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h24, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h1, h26, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h1, h23, h28, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi1]
                        · rcases h2bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hc12, hlam, hphi, p30_1, u2elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30_1, u2elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            rcases p30_3 (m.d 0 2) (by simp) with h34 | h34
                            · rcases p30_3 (m.d 1 2) (by simp) with h35 | h35
                              · rcases p30_3 (m.d 2 3) (by simp) with h36 | h36
                                · linarith only [h0, h36, hlam]
                                · linarith only [h23, h36, hlam]
                              · linarith only [h35, h4, hlam]
                            · linarith only [h34, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h23, h24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30_1, u2elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hc02, hlam, hphi, p30_1, u2elo1]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30_1, u2elo1]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            rcases p30_3 (m.d 0 2) (by simp) with h45 | h45
                            · rcases p30_3 (m.d 1 2) (by simp) with h46 | h46
                              · rcases p30_3 (m.d 2 3) (by simp) with h47 | h47
                                · linarith only [h3, h47, hlam]
                                · linarith only [h23, h47, hlam]
                              · linarith only [h46, hlam, p30_0]
                            · linarith only [h1, h45, hlam]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h23, h24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30_1, u2elo1]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h0, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h3, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h0, h23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30_1, u2elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h24, hlam, p30_1]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h1, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h4, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h23, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h26, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h2, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h5, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p30_1, u2elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h2, h23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30_1, u2elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                    · linarith only [h0, h68, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                      · linarith only [h23, h3, h6, h7, h70, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                        · linarith only [h6, h7, h72, hlam]
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
                            linarith only [hc12, hlam, hphi, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h77 | h77
                            · rcases p74_3 (m.d 1 2) (by simp) with h78 | h78
                              · rcases p74_3 (m.d 2 3) (by simp) with h79 | h79
                                · linarith only [h79, hlam, p74_0]
                                · rcases p74_3 (m.d 2 4) (by simp) with h81 | h81
                                  · linarith only [h1, h81, hlam]
                                  · linarith only [h23, h81, hlam]
                              · linarith only [h3, h78, hlam]
                            · linarith only [h77, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h86 | h86
                            · rcases p74_3 (m.d 1 2) (by simp) with h87 | h87
                              · rcases p74_3 (m.d 2 3) (by simp) with h88 | h88
                                · linarith only [h0, h88, hlam]
                                · rcases p74_3 (m.d 2 4) (by simp) with h90 | h90
                                  · linarith only [h90, hlam, p74_0]
                                  · rcases p74_3 (m.d 2 5) (by simp) with h92 | h92
                                    · linarith only [h2, h92, hlam]
                                    · linarith only [h70, h92, hlam]
                              · linarith only [h4, h87, hlam]
                            · linarith only [h86, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p74_1, u2elo0, u5ehi2]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hc02, hlam, hphi, p74_1, u2elo1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h100 | h100
                            · rcases p74_3 (m.d 1 2) (by simp) with h101 | h101
                              · rcases p74_3 (m.d 2 3) (by simp) with h102 | h102
                                · linarith only [h102, hlam, p74_0]
                                · rcases p74_3 (m.d 2 4) (by simp) with h104 | h104
                                  · linarith only [h104, h4, hlam]
                                  · linarith only [h104, h23, hlam]
                              · linarith only [h101, hlam, p74_0]
                            · linarith only [h0, h100, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h109 | h109
                            · rcases p74_3 (m.d 1 2) (by simp) with h110 | h110
                              · rcases p74_3 (m.d 2 3) (by simp) with h111 | h111
                                · linarith only [h111, h3, hlam]
                                · rcases p74_3 (m.d 2 4) (by simp) with h113 | h113
                                  · linarith only [h113, hlam, p74_0]
                                  · rcases p74_3 (m.d 2 5) (by simp) with h115 | h115
                                    · linarith only [h115, h5, hlam]
                                    · linarith only [h115, h70, hlam]
                              · linarith only [h110, hlam, p74_0]
                            · linarith only [h1, h109, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p74_1, u2elo1, u5ehi2]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h3, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h23, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h68, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h1, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h4, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h70, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h2, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h5, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                  · linarith only [h0, h137, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h0, h139, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                      · linarith only [h1, h141, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                        · rcases h2bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hc12, hlam, hphi, p144_1, u2elo0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            rcases p144_3 (m.d 0 2) (by simp) with h147 | h147
                            · rcases p144_3 (m.d 1 2) (by simp) with h148 | h148
                              · rcases p144_3 (m.d 2 3) (by simp) with h149 | h149
                                · linarith only [h149, hlam, p144_0]
                                · rcases p144_3 (m.d 2 4) (by simp) with h151 | h151
                                  · linarith only [h1, h151, hlam]
                                  · linarith only [h137, h151, hlam]
                              · linarith only [h148, h3, hlam]
                            · linarith only [h147, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            rcases p144_3 (m.d 0 2) (by simp) with h156 | h156
                            · rcases p144_3 (m.d 1 2) (by simp) with h157 | h157
                              · rcases p144_3 (m.d 2 3) (by simp) with h158 | h158
                                · linarith only [h0, h158, hlam]
                                · rcases p144_3 (m.d 2 4) (by simp) with h160 | h160
                                  · linarith only [h160, hlam, p144_0]
                                  · rcases p144_3 (m.d 2 5) (by simp) with h162 | h162
                                    · linarith only [h162, h2, hlam]
                                    · linarith only [h141, h162, hlam]
                              · linarith only [h157, h4, hlam]
                            · linarith only [h156, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo0, u5ehi2]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hc02, hlam, hphi, p144_1, u2elo1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            rcases p144_3 (m.d 0 2) (by simp) with h170 | h170
                            · rcases p144_3 (m.d 1 2) (by simp) with h171 | h171
                              · rcases p144_3 (m.d 2 3) (by simp) with h172 | h172
                                · linarith only [h172, hlam, p144_0]
                                · rcases p144_3 (m.d 2 4) (by simp) with h174 | h174
                                  · linarith only [h174, h4, hlam]
                                  · linarith only [h137, h174, hlam]
                              · linarith only [h171, hlam, p144_0]
                            · linarith only [h0, h170, hlam]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            rcases p144_3 (m.d 0 2) (by simp) with h179 | h179
                            · rcases p144_3 (m.d 1 2) (by simp) with h180 | h180
                              · rcases p144_3 (m.d 2 3) (by simp) with h181 | h181
                                · linarith only [h181, h3, hlam]
                                · rcases p144_3 (m.d 2 4) (by simp) with h183 | h183
                                  · linarith only [h183, hlam, p144_0]
                                  · rcases p144_3 (m.d 2 5) (by simp) with h185 | h185
                                    · linarith only [h185, h5, hlam]
                                    · linarith only [h141, h185, hlam]
                              · linarith only [h180, hlam, p144_0]
                            · linarith only [h1, h179, hlam]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo1, u5ehi2]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h0, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h3, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h137, hlam, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h139, hlam, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h1, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h4, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h136, h141, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p144_1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h141, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h2, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h5, hlam, p144_0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p144_1, u2elo0]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [h136, h137, h141, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p144_1, u2elo1]
                          · have p144_0 := h144c.1
                            have p144_1 := h144c.2.1
                            have p144_2 := h144c.2.2.1
                            have p144_3 := h144c.2.2.2
                            linarith only [hlam, p144_0]
                        · linarith only [h136, h143, h3, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                  · linarith only [h207, h3, h6, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                    · linarith only [h1, h207, h209, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h211 | h211
                      · linarith only [h1, h211, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h213 | h213
                        · rcases h2bigk with h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hc12, hlam, hphi, p214_1, u2elo0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            rcases p214_3 (m.d 0 2) (by simp) with h217 | h217
                            · rcases p214_3 (m.d 1 2) (by simp) with h218 | h218
                              · rcases p214_3 (m.d 2 3) (by simp) with h219 | h219
                                · linarith only [h219, hlam, p214_0]
                                · rcases p214_3 (m.d 2 4) (by simp) with h221 | h221
                                  · linarith only [h1, h221, hlam]
                                  · linarith only [h207, h221, hlam]
                              · linarith only [h218, h3, hlam]
                            · linarith only [h217, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            rcases p214_3 (m.d 0 2) (by simp) with h226 | h226
                            · rcases p214_3 (m.d 1 2) (by simp) with h227 | h227
                              · rcases p214_3 (m.d 2 3) (by simp) with h228 | h228
                                · linarith only [h0, h228, hlam]
                                · rcases p214_3 (m.d 2 4) (by simp) with h230 | h230
                                  · linarith only [h230, hlam, p214_0]
                                  · rcases p214_3 (m.d 2 5) (by simp) with h232 | h232
                                    · linarith only [h2, h232, hlam]
                                    · linarith only [h211, h232, hlam]
                              · linarith only [h227, h4, hlam]
                            · linarith only [h226, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p214_1, u2elo0, u5ehi2]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hc02, hlam, hphi, p214_1, u2elo1]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            rcases p214_3 (m.d 0 2) (by simp) with h240 | h240
                            · rcases p214_3 (m.d 1 2) (by simp) with h241 | h241
                              · rcases p214_3 (m.d 2 3) (by simp) with h242 | h242
                                · linarith only [h242, hlam, p214_0]
                                · rcases p214_3 (m.d 2 4) (by simp) with h244 | h244
                                  · linarith only [h244, h4, hlam]
                                  · linarith only [h207, h244, hlam]
                              · linarith only [h241, hlam, p214_0]
                            · linarith only [h0, h240, hlam]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            rcases p214_3 (m.d 0 2) (by simp) with h249 | h249
                            · rcases p214_3 (m.d 1 2) (by simp) with h250 | h250
                              · rcases p214_3 (m.d 2 3) (by simp) with h251 | h251
                                · linarith only [h251, h3, hlam]
                                · rcases p214_3 (m.d 2 4) (by simp) with h253 | h253
                                  · linarith only [h253, hlam, p214_0]
                                  · rcases p214_3 (m.d 2 5) (by simp) with h255 | h255
                                    · linarith only [h255, h5, hlam]
                                    · linarith only [h211, h255, hlam]
                              · linarith only [h250, hlam, p214_0]
                            · linarith only [h1, h249, hlam]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p214_1, u2elo1, u5ehi2]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h0, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h3, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h207, hlam, p214_1]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h209, hlam, p214_1]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h1, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h4, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p214_1, u2elo0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h211, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h2, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h5, hlam, p214_0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p214_1, u2elo0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p214_1, u2elo0]
                          · have p214_0 := h214c.1
                            have p214_1 := h214c.2.1
                            have p214_2 := h214c.2.2.1
                            have p214_3 := h214c.2.2.2
                            linarith only [hlam, p214_0]
                        · rcases h2bigk with h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hc12, hlam, hphi, p276_1, u2elo0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            rcases p276_3 (m.d 0 2) (by simp) with h279 | h279
                            · rcases p276_3 (m.d 1 2) (by simp) with h280 | h280
                              · rcases p276_3 (m.d 2 3) (by simp) with h281 | h281
                                · linarith only [h281, hlam, p276_0]
                                · rcases p276_3 (m.d 2 4) (by simp) with h283 | h283
                                  · linarith only [h1, h283, hlam]
                                  · linarith only [h207, h283, hlam]
                              · linarith only [h280, h3, hlam]
                            · linarith only [h279, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            rcases p276_3 (m.d 0 2) (by simp) with h288 | h288
                            · rcases p276_3 (m.d 1 2) (by simp) with h289 | h289
                              · rcases p276_3 (m.d 2 3) (by simp) with h290 | h290
                                · linarith only [h0, h290, hlam]
                                · rcases p276_3 (m.d 2 4) (by simp) with h292 | h292
                                  · linarith only [h292, hlam, p276_0]
                                  · rcases p276_3 (m.d 2 5) (by simp) with h294 | h294
                                    · linarith only [h2, h294, hlam]
                                    · linarith only [h211, h294, hlam]
                              · linarith only [h289, h4, hlam]
                            · linarith only [h288, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p276_1, u2elo0, u5ehi2]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hc02, hlam, hphi, p276_1, u2elo1]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            rcases p276_3 (m.d 0 2) (by simp) with h302 | h302
                            · rcases p276_3 (m.d 1 2) (by simp) with h303 | h303
                              · rcases p276_3 (m.d 2 3) (by simp) with h304 | h304
                                · linarith only [h304, hlam, p276_0]
                                · rcases p276_3 (m.d 2 4) (by simp) with h306 | h306
                                  · linarith only [h306, h4, hlam]
                                  · linarith only [h207, h306, hlam]
                              · linarith only [h303, hlam, p276_0]
                            · linarith only [h0, h302, hlam]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            rcases p276_3 (m.d 0 2) (by simp) with h311 | h311
                            · rcases p276_3 (m.d 1 2) (by simp) with h312 | h312
                              · rcases p276_3 (m.d 2 3) (by simp) with h313 | h313
                                · linarith only [h3, h313, hlam]
                                · rcases p276_3 (m.d 2 4) (by simp) with h315 | h315
                                  · linarith only [h315, hlam, p276_0]
                                  · rcases p276_3 (m.d 2 5) (by simp) with h317 | h317
                                    · linarith only [h317, h5, hlam]
                                    · linarith only [h211, h317, hlam]
                              · linarith only [h312, hlam, p276_0]
                            · linarith only [h1, h311, hlam]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p276_1, u2elo1, u5ehi2]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h0, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h3, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h207, hlam, p276_1]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h209, hlam, p276_1]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h1, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h4, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p276_1, u2elo0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h211, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h2, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h5, hlam, p276_0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p276_1, u2elo0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p276_1, u2elo0]
                          · have p276_0 := h276c.1
                            have p276_1 := h276c.2.1
                            have p276_2 := h276c.2.2.1
                            have p276_3 := h276c.2.2.2
                            linarith only [hlam, p276_0]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h1, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · linarith only [h0, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
        · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
          · rcases m.htr 1 2 5 (by decide) (by decide) with h343 | h343
            · linarith only [h2, h343, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
              · rcases m.htr 1 4 5 (by decide) (by decide) with h346 | h346
                · linarith only [h342, h343, h346, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                  · linarith only [h0, h2, h348, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h341, h343, h345, h348, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h351 | h351
                · linarith only [h342, h343, h351, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                  · linarith only [h0, h2, h345, h353, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                    · linarith only [h0, h2, h355, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h357 | h357
                      · linarith only [h1, h2, h351, h357, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                        · linarith only [h1, h2, h353, h357, h359, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, p361_1, u2elo4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p361_1, u2elo4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p361_1, u2elo4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h2, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hc02, hlam, hphi, p361_1, u2elo1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h343, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p361_1, u2elo4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h343, h353, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p361_1, u2elo4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h343, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h0, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h341, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h353, hlam, p361_1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h355, hlam, p361_1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h1, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h342, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p361_1, u2elo0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h357, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hc02, hlam, hphi, p361_1, u2elo4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hc12, hlam, hphi, p361_1, u2elo4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            rcases p361_3 (m.d 0 2) (by simp) with h384 | h384
                            · linarith only [h2, h384, hlam]
                            · linarith only [h0, h384, hlam]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            rcases p361_3 (m.d 0 2) (by simp) with h387 | h387
                            · linarith only [h2, h387, hlam]
                            · linarith only [h1, h387, hlam]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
          · linarith only [h1, h342, hc12, hlam, hphi, u2elo0]
        · linarith only [h0, h2, h341, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h393 | h393
      · linarith only [h1, h393, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
        · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
          · linarith only [h1, h396, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
            · linarith only [h0, h393, h396, h398, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
              · linarith only [h395, h396, h400, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h402 | h402
                · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                  · linarith only [h0, h400, h403, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h405 | h405
                    · linarith only [h0, h1, h405, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                        · rcases h2bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h393, h407, hc12, hlam, hphi, p409_1, u2elo3]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h393, h407, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p409_1, u2elo3]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h1, hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h393, hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hc02, hlam, hphi, p409_1, u2elo1]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h396, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p409_1, u2elo3]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h396, hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h398, hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h0, hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h395, hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h403, hlam, p409_1]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h405, hlam, p409_1]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p409_1, u2elo3]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hc12, hlam, hphi, p409_1, u2elo3]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            rcases p409_3 (m.d 0 2) (by simp) with h427 | h427
                            · linarith only [h1, h427, hlam]
                            · linarith only [h0, h427, hlam]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hlam, p409_0]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p409_1, u2elo3, u5ehi2]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p409_1, u2elo4]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h395, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p409_1, u2elo4]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            rcases p409_3 (m.d 0 2) (by simp) with h434 | h434
                            · linarith only [h393, h434, hlam]
                            · linarith only [h0, h434, hlam]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [h407, hlam, p409_1]
                          · have p409_0 := h409c.1
                            have p409_1 := h409c.2.1
                            have p409_2 := h409c.2.2.1
                            have p409_3 := h409c.2.2.2
                            linarith only [hlam, p409_0]
                        · linarith only [h0, h1, h402, h403, h408, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h396, h402, h407, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h441 | h441
                  · linarith only [h0, h1, h441, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h443 | h443
                    · linarith only [h0, h1, h443, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h445 | h445
                      · linarith only [h396, h402, h445, hc12, hlam, hphi, u2elo3]
                      · linarith only [h0, h1, h445, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h1, h395, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h449 | h449
    · rcases m.htr 0 2 5 (by decide) (by decide) with h450 | h450
      · linarith only [h0, h450, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h452 | h452
        · linarith only [h0, h452, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h454 | h454
          · rcases m.htr 1 2 5 (by decide) (by decide) with h455 | h455
            · linarith only [h449, h450, h452, h455, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
              · rcases m.htr 1 4 5 (by decide) (by decide) with h458 | h458
                · linarith only [h452, h454, h458, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h462 | h462
                      · linarith only [h449, h458, h462, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h464 | h464
                        · linarith only [h450, h460, h462, h464, hc02, hlam, hphi, u2elo3]
                        · rcases h2bigk with h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h450, h461, hc12, hlam, hphi, p466_1, u2elo2]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h0, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h450, h461, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p466_1, u2elo2]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h450, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hc02, hlam, hphi, p466_1, u2elo1]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h452, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h452, h460, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p466_1, u2elo2]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h455, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h449, h460, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p466_1, u2elo2]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hc12, hlam, hphi, p466_1, u2elo2]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            rcases p466_3 (m.d 0 2) (by simp) with h480 | h480
                            · linarith only [h0, h480, hlam]
                            · linarith only [h449, h480, hlam]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p466_1, u2elo2, u5ehi2]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h449, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h454, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h460, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h462, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h449, h460, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p466_1, u2elo4]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h454, h460, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p466_1, u2elo4]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [h461, hlam, p466_0]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            rcases p466_3 (m.d 0 2) (by simp) with h492 | h492
                            · linarith only [h450, h492, hlam]
                            · linarith only [h449, h492, hlam]
                          · have p466_0 := h466c.1
                            have p466_1 := h466c.2.1
                            have p466_2 := h466c.2.2.1
                            have p466_3 := h466c.2.2.2
                            linarith only [hlam, p466_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h496 | h496
                      · linarith only [h449, h496, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h498 | h498
                        · linarith only [h449, h460, h496, h498, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
                        · linarith only [h0, h449, h460, h461, h498, hc34, hc45, hlam, hphi]
                  · linarith only [h452, h457, h460, hlam]
              · linarith only [h452, h454, h457, hlam]
          · linarith only [h0, h449, h454, hc12, hlam, hphi, u2elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h504 | h504
      · linarith only [h0, h504, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h506 | h506
        · linarith only [h0, h506, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h508 | h508
          · linarith only [h449, h506, h508, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h510 | h510
            · linarith only [h504, h506, h510, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
              · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h515 | h515
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h516 | h516
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h517 | h517
                        · linarith only [h506, h512, h517, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                        · rcases h2bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc12, hlam, hphi, p519_1, u2elo0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h0, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h449, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h504, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc02, hlam, hphi, p519_1, u2elo1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h506, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h508, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h510, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc02, hlam, hphi, p519_1, u2elo2]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc12, hlam, hphi, p519_1, u2elo2]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h516, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u2elo2, u5ehi2]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h504, hc02, hlam, hphi, p519_1, u2elo2]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc02, hlam, hphi, p519_1, u2elo3]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc12, hlam, hphi, p519_1, u2elo3]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h514, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h504, h514, hc02, hlam, hphi, p519_1, u2elo2]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc02, hlam, hphi, p519_1, u2elo4]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hc12, hlam, hphi, p519_1, u2elo4]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h515, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h516, hlam, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                      · linarith only [h508, h513, h516, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                      · linarith only [h514, h515, h546, hlam]
                      · linarith only [h449, h506, h512, h513, h515, h546, hc02, hc35, hlam, hphi, ht23]
                  · linarith only [h506, h512, h514, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h551 | h551
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h552 | h552
                      · linarith only [h508, h513, h552, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h554 | h554
                        · linarith only [h449, h552, h554, hc02, hc34, hlam, hphi, ht23]
                        · rcases h2bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h449, hc12, hlam, hphi, p556_1, u2elo3]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h0, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h449, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h504, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hc02, hlam, hphi, p556_1, u2elo1]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h506, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h508, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h510, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hc02, hlam, hphi, p556_1, u2elo2]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hc12, hlam, hphi, p556_1, u2elo2]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h449, hc02, hlam, hphi, p556_1, u2elo2]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h510, hlam, hphi, ht01, ht0b, ht12, ht5b, p556_1, u2elo2, u5ehi1]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hc02, hlam, hphi, p556_1, u2elo3]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hc12, hlam, hphi, p556_1, u2elo3]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h550, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h552, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hc02, hlam, hphi, p556_1, u2elo4]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hc12, hlam, hphi, p556_1, u2elo4]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h551, hlam, p556_0]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [h449, h551, hc02, hlam, hphi, p556_1, u2elo2]
                          · have p556_0 := h556c.1
                            have p556_1 := h556c.2.1
                            have p556_2 := h556c.2.2.1
                            have p556_3 := h556c.2.2.2
                            linarith only [hlam, p556_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h582 | h582
                      · linarith only [h508, h513, h582, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h584 | h584
                        · linarith only [h449, h582, h584, hc02, hc34, hlam, hphi, ht23]
                        · rcases h2bigk with h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h449, hc12, hlam, hphi, p586_1, u2elo3]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h0, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h449, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h504, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hc02, hlam, hphi, p586_1, u2elo1]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h506, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h508, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h510, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h551, h584, hc02, hc45, hlam, hphi, ht23, ht34, p586_1]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h551, h584, hc12, hc45, hlam, hphi, ht23, ht34, p586_1]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h551, h584, hc24, hc45, hlam, hphi, p586_1]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h551, hlam, p586_1]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hc02, hlam, hphi, p586_1, u2elo3]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hc12, hlam, hphi, p586_1, u2elo3]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h550, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h582, hlam, p586_0]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hc02, hlam, hphi, p586_1, u2elo4]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hc12, hlam, hphi, p586_1, u2elo4]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h0, hc02, hlam, hphi, p586_1, u2elo4]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [h449, hc02, hlam, hphi, p586_1, u2elo4]
                          · have p586_0 := h586c.1
                            have p586_1 := h586c.2.1
                            have p586_2 := h586c.2.2.1
                            have p586_3 := h586c.2.2.2
                            linarith only [hlam, p586_0]
                  · linarith only [h0, h508, h512, h550, hc02, hlam, hphi, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
                · rcases m.htr 2 3 4 (by decide) (by decide) with h614 | h614
                  · linarith only [h506, h512, h614, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h616 | h616
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h618 | h618
                        · rcases h2bigk with h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hc12, hlam, hphi, p619_1, u2elo0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h0, hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h449, hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h504, hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hc02, hlam, hphi, p619_1, u2elo1]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h506, hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h508, hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h510, hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h614, hc02, hc34, hlam, hphi, ht23, p619_1]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h614, hc12, hc34, hlam, hphi, ht23, p619_1]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h614, hlam, p619_1]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h614, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p619_1, u5ehi2]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hc02, hlam, hphi, p619_1, u2elo3]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hc12, hlam, hphi, p619_1, u2elo3]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h616, hlam, hphi, ht01, ht0b, ht12, ht5b, p619_1, u2elo3, u5ehi3]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h504, hc02, hlam, hphi, p619_1, u2elo3]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hc02, hlam, hphi, p619_1, u2elo4]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hc12, hlam, hphi, p619_1, u2elo4]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h616, hlam, p619_0]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [h617, hlam, p619_1]
                          · have p619_0 := h619c.1
                            have p619_1 := h619c.2.1
                            have p619_2 := h619c.2.2.1
                            have p619_3 := h619c.2.2.2
                            linarith only [hlam, p619_0]
                        · linarith only [h613, h614, h616, h618, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h508, h613, h617, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h648 | h648
                        · rcases h2bigk with h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hc12, hlam, hphi, p649_1, u2elo0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h0, hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h449, hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h504, hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hc02, hlam, hphi, p649_1, u2elo1]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h506, hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h508, hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h510, hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hc02, hlam, hphi, p649_1, u2elo2]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h616, h648, hc12, hc34, hlam, hphi, ht23, p649_1]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h614, hlam, p649_1]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h616, hlam, p649_1]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hc02, hlam, hphi, p649_1, u2elo3]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hc12, hlam, hphi, p649_1, u2elo3]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h0, hc02, hlam, hphi, p649_1, u2elo3]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hlam, p649_0]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p649_1, u2elo3, u5ehi2]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hc02, hlam, hphi, p649_1, u2elo4]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hc12, hlam, hphi, p649_1, u2elo4]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h0, hc02, hlam, hphi, p649_1, u2elo4]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [h647, hlam, p649_1]
                          · have p649_0 := h649c.1
                            have p649_1 := h649c.2.1
                            have p649_2 := h649c.2.2.1
                            have p649_3 := h649c.2.2.2
                            linarith only [hlam, p649_0]
                        · linarith only [h506, h508, h512, h613, h648, hc12, hlam, hphi, u2elo3]
                      · linarith only [h508, h613, h647, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                  · linarith only [h506, h512, h677, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h679 | h679
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                      · linarith only [h508, h613, h680, hc12, hlam, hphi, u2elo3]
                      · linarith only [h677, h679, h680, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h683 | h683
                      · linarith only [h506, h512, h613, h683, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h685 | h685
                        · linarith only [h0, h677, h683, h685, hc02, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h677, h685, hc02, hc45, hlam, hphi, ht23, ht34]

end R2N4
