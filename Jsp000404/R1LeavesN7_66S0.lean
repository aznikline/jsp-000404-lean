import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
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
                          · linarith only [h0, h12, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h12, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h19, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h19, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h17, h18, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h17, h4, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h24, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h0, h28, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h26, h28, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h26, h27, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h26, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h0, h37, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h37, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h35, h36, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h35, h4, hc12, hlam, hphi, u2elo0]
                    · linarith only [h33, h34, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h46, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h46, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h44, h45, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h4, h44, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                          · linarith only [h0, h53, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                          · linarith only [h53, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h5, h51, h52, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h4, h51, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 0 3 5 (by decide) (by decide) with h59 | h59
                  · linarith only [h4, h59, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
                    · linarith only [h4, h58, h6, h61, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h6, h65, hc02, hlam, hphi, u2elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h1, h59, h68, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                                · linarith only [h2, h61, h70, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                                  · linarith only [h0, h6, h63, h72, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                                  · linarith only [h4, h58, h6, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                            · linarith only [h4, h58, h6, h67, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h5, h6, h64, hc12, hlam, hphi, u2elo4]
                      · linarith only [h4, h6, h63, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h78 | h78
                  · linarith only [h4, h6, h78, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h5, h6, h80, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                          · linarith only [h6, h84, hc02, hlam, hphi, u2elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                            · linarith only [h1, h58, h86, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                              · linarith only [h1, h78, h88, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h2, h80, h90, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                                  · linarith only [h0, h58, h6, h82, h92, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                                    · linarith only [h1, h78, h82, h94, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                                      · linarith only [h0, h58, h6, h80, h83, h96, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                                        · linarith only [h4, h6, h96, h98, hc23, hc34, hlam, hphi]
                                        · rcases h3bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h4, h6, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u2elo4]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u2elo4]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h58, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h78, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h1, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h86, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h88, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h4, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h82, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h92, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h94, hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h98, hc03, hc45, hlam, hphi, ht34, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h82, h98, hc23, hc45, hlam, hphi, ht34, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h98, hc23, hc45, hlam, hphi, ht34, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h98, hlam, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            rcases p100_3 (m.d 0 3) (by simp) with h121 | h121
                                            · linarith only [h121, hlam, p100_0]
                                            · rcases p100_3 (m.d 1 3) (by simp) with h123 | h123
                                              · linarith only [h123, h88, hlam]
                                              · rcases p100_3 (m.d 2 3) (by simp) with h125 | h125
                                                · linarith only [h125, h94, hlam]
                                                · rcases p100_3 (m.d 3 4) (by simp) with h127 | h127
                                                  · linarith only [h127, h98, hlam]
                                                  · linarith only [h127, h58, hlam]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            rcases p100_3 (m.d 0 3) (by simp) with h130 | h130
                                            · linarith only [h130, h78, hlam]
                                            · linarith only [h1, h130, hlam]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            rcases p100_3 (m.d 0 3) (by simp) with h133 | h133
                                            · linarith only [h133, h78, hlam]
                                            · linarith only [h133, h4, hlam]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [h1, h58, h82, hc23, hc35, hlam, hphi, p100_1]
                                          · have p100_0 := h100c.1
                                            have p100_1 := h100c.2.1
                                            have p100_2 := h100c.2.2.1
                                            have p100_3 := h100c.2.2.2
                                            linarith only [hlam, p100_0]
                        · linarith only [h5, h6, h83, hc12, hlam, hphi, u2elo4]
                      · linarith only [h4, h6, h82, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h140 | h140
              · linarith only [h140, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
                · linarith only [h142, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h144 | h144
                  · linarith only [h144, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
                        · linarith only [h148, h5, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                          · linarith only [h0, h140, h150, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                            · linarith only [h1, h142, h152, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                              · linarith only [h1, h144, h154, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                                · linarith only [h156, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · linarith only [h146, h147, h148, h156, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h140, h147, h4, hc12, hlam, hphi, u2elo4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
                        · linarith only [h161, h5, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                          · linarith only [h0, h163, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                            · linarith only [h0, h142, h160, h165, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h167 | h167
                              · linarith only [h1, h144, h167, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
                                · linarith only [h169, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
                                  · linarith only [h142, h171, h4, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                                    · linarith only [h1, h144, h160, h173, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h175 | h175
                                      · linarith only [h146, h160, h161, h175, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                      · linarith only [h0, h160, h175, h5, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h160, h4, h5, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h179 | h179
            · rcases m.htr 0 2 5 (by decide) (by decide) with h180 | h180
              · linarith only [h180, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
                · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h184 | h184
                    · linarith only [h179, h184, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
                      · linarith only [h186, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                          · linarith only [h0, h189, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                              · linarith only [h1, h192, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h183, h191, h192, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h182, h186, h191, h4, hc12, hlam, hphi, u2elo2]
                        · linarith only [h179, h188, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
                    · linarith only [h179, h197, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                      · linarith only [h199, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h202 | h202
                          · linarith only [h0, h180, h202, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h204 | h204
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h205 | h205
                              · linarith only [h1, h183, h205, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h207 | h207
                                · linarith only [h197, h2, h207, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h210 | h210
                                    · linarith only [h1, h183, h199, h201, h209, h210, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h212 | h212
                                      · linarith only [h0, h197, h201, h212, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h214 | h214
                                        · linarith only [h0, h180, h201, h209, h210, h212, h214, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                        · linarith only [h0, h201, h210, h214, h4, hc24, hc45, hlam, hphi]
                                  · linarith only [h0, h182, h201, h209, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h179, h182, h199, h201, h204, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · linarith only [h179, h201, h4, hc12, hlam, hphi, u2elo2]
                · linarith only [h179, h182, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h221 | h221
              · linarith only [h221, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
                · rcases m.htr 0 3 5 (by decide) (by decide) with h224 | h224
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                      · linarith only [h226, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
                        · linarith only [h0, h179, h225, h228, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h230 | h230
                          · linarith only [h0, h221, h230, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h233 | h233
                              · linarith only [h1, h233, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h224, h232, h233, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h223, h226, h232, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                      · linarith only [h237, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                        · linarith only [h0, h179, h239, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h0, h221, h241, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                              · linarith only [h1, h244, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h224, h243, h244, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h223, h237, h243, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h248 | h248
                    · linarith only [h223, h224, h248, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                      · linarith only [h250, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                        · linarith only [h0, h179, h252, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h0, h179, h254, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                              · linarith only [h1, h224, h257, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                                · linarith only [h1, h256, h259, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h262 | h262
                                    · linarith only [h224, h262, h4, hc02, hlam, hphi, u2elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h264 | h264
                                      · linarith only [h0, h179, h248, h261, h262, h264, hc12, hc35, hlam, hphi, ht23]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                                        · linarith only [h1, h256, h264, h266, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                        · rcases h3bigk with h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h221, h224, h256, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p268_1, u2elo4]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h4, hlam, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h262, h266, h4, hc34, hc45, hlam, hphi, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h224, hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h1, hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h250, hlam, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p268_1, u0elo0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h257, hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h262, h266, hc03, hc45, hlam, hphi, ht34, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h262, h266, hc13, hc45, hlam, hphi, ht34, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h262, h266, hc34, hc45, hlam, hphi, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h262, hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h223, hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h256, hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h261, hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [hlam, p268_0]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h266, hlam, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h1, h256, h266, hc34, hc45, hlam, hphi, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h256, h266, hc34, hc45, hlam, hphi, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [h0, h266, h4, hc12, hc45, hlam, hphi, ht23, ht34, p268_1]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            rcases p268_3 (m.d 0 3) (by simp) with h292 | h292
                                            · linarith only [h224, h292, hlam]
                                            · linarith only [h223, h292, hlam]
                                          · have p268_0 := h268c.1
                                            have p268_1 := h268c.2.1
                                            have p268_2 := h268c.2.2.1
                                            have p268_3 := h268c.2.2.2
                                            linarith only [hlam, p268_0]
                                  · linarith only [h1, h256, h261, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h223, h224, h256, hc13, hc35, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
                      · linarith only [h0, h300, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
                        · linarith only [h0, h179, h223, h298, h302, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                          · linarith only [h0, h304, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                            · linarith only [h223, h298, h306, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                              · linarith only [h2, h306, h308, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                              · linarith only [h223, h298, h308, hc13, hc34, hlam, hphi]
                    · linarith only [h223, h298, h299, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                      · linarith only [h0, h313, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
                        · linarith only [h0, h179, h315, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                          · linarith only [h0, h221, h317, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                            · linarith only [h1, h223, h319, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
                              · linarith only [h1, h298, h321, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                                · linarith only [h2, h323, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                · linarith only [h179, h312, h315, h323, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                      · linarith only [h0, h326, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                        · linarith only [h0, h179, h328, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                          · linarith only [h0, h221, h330, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                            · linarith only [h1, h223, h332, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                              · linarith only [h1, h298, h334, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                                · linarith only [h2, h312, h336, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h338 | h338
                                  · linarith only [h223, h338, h4, hc02, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h340 | h340
                                    · linarith only [h0, h298, h340, h4, hc12, hlam, hphi, u2elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h342 | h342
                                      · linarith only [h0, h179, h312, h342, hc12, hlam, hphi, u2elo3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h344 | h344
                                        · linarith only [h0, h338, h342, h344, h4, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h0, h338, h344, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h347 | h347
          · rcases m.htr 0 2 4 (by decide) (by decide) with h348 | h348
            · rcases m.htr 0 2 5 (by decide) (by decide) with h349 | h349
              · linarith only [h0, h3, h349, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h351 | h351
                · rcases m.htr 0 3 5 (by decide) (by decide) with h352 | h352
                  · linarith only [h347, h349, h352, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h354 | h354
                    · linarith only [h348, h349, h354, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h357 | h357
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
                          · linarith only [h0, h349, h358, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h3, h358, hc12, hlam, hphi, u2elo4]
                        · linarith only [h348, h349, h356, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h347, h349, h356, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
                  · linarith only [h347, h349, h363, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h365 | h365
                    · linarith only [h348, h349, h365, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h368 | h368
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h369 | h369
                          · linarith only [h349, h369, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h3, h367, h369, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h348, h367, h368, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h347, h367, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h374 | h374
              · linarith only [h348, h374, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h376 | h376
                · linarith only [h347, h348, h376, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h378 | h378
                  · linarith only [h347, h348, h378, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h380 | h380
                    · linarith only [h2, h3, h380, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                        · linarith only [h0, h348, h383, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h385 | h385
                          · linarith only [h0, h348, h374, h385, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                          · linarith only [h2, h3, h382, h383, h385, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h347, h348, h382, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h389 | h389
            · rcases m.htr 0 2 5 (by decide) (by decide) with h390 | h390
              · linarith only [h347, h390, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
                · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                  · linarith only [h1, h3, h393, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h395 | h395
                    · linarith only [h347, h389, h395, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h397 | h397
                      · linarith only [h347, h397, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                          · linarith only [h1, h3, h390, h397, h400, hlam]
                          · linarith only [h1, h3, h397, h400, hc12, hlam, hphi, u2elo4]
                        · linarith only [h347, h389, h399, hc12, hlam, hphi, u2elo2]
                · linarith only [h347, h389, h392, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h405 | h405
              · linarith only [h389, h405, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
                · rcases m.htr 0 3 5 (by decide) (by decide) with h408 | h408
                  · linarith only [h1, h3, h408, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
                    · linarith only [h1, h3, h407, h410, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                      · linarith only [h0, h347, h412, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                        · linarith only [h0, h389, h414, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h416 | h416
                          · linarith only [h0, h3, h389, h405, h416, hc01, hlam, hphi, ht12, u2elo3]
                          · linarith only [h0, h3, h416, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h419 | h419
                  · linarith only [h2, h3, h407, h419, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h2, h3, h421, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h423 | h423
                      · linarith only [h347, h423, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h425 | h425
                        · linarith only [h0, h389, h425, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
                          · linarith only [h1, h3, h423, h427, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                          · linarith only [h0, h3, h427, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h430 | h430
        · rcases m.htr 0 2 3 (by decide) (by decide) with h431 | h431
          · rcases m.htr 0 2 4 (by decide) (by decide) with h432 | h432
            · linarith only [h0, h2, h432, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h434 | h434
              · linarith only [h432, h434, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h436 | h436
                · linarith only [h2, h430, h431, h432, h436, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h438 | h438
                  · linarith only [h431, h432, h438, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h440 | h440
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                        · linarith only [h0, h432, h442, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h2, h441, h442, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h431, h434, h441, hc12, hlam, hphi, u2elo4]
                    · linarith only [h2, h430, h440, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h447 | h447
            · linarith only [h2, h430, h431, h447, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h449 | h449
              · linarith only [h431, h449, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h451 | h451
                · linarith only [h1, h2, h451, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
                      · linarith only [h431, h455, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
                        · linarith only [h0, h1, h2, h447, h453, h457, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h1, h2, h453, h457, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                    · linarith only [h1, h2, h453, h454, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                      · linarith only [h431, h462, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                        · linarith only [h0, h447, h464, hlam]
                        · linarith only [h1, h2, h462, h464, hc12, hlam, hphi, u2elo3]
                    · linarith only [h2, h430, h461, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h468 | h468
          · rcases m.htr 0 2 4 (by decide) (by decide) with h469 | h469
            · linarith only [h0, h2, h469, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h471 | h471
              · linarith only [h469, h471, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h473 | h473
                · linarith only [h0, h2, h468, h469, h473, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h475 | h475
                  · linarith only [h468, h469, h475, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h477 | h477
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
                        · linarith only [h469, h479, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h2, h478, h479, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h468, h471, h478, hc12, hlam, hphi, u2elo4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
                      · linarith only [h0, h2, h477, h483, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h468, h471, h483, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h486 | h486
            · linarith only [h0, h2, h468, h486, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h488 | h488
              · linarith only [h468, h488, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h490 | h490
                · linarith only [h1, h2, h490, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h492 | h492
                  · linarith only [h1, h430, h492, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h494 | h494
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h495 | h495
                      · linarith only [h468, h495, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h497 | h497
                        · linarith only [h1, h486, h494, h495, h497, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                        · linarith only [h1, h2, h495, h497, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
                      · linarith only [h0, h468, h500, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h502 | h502
                        · linarith only [h0, h2, h486, h502, hlam]
                        · linarith only [h1, h2, h500, h502, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h505 | h505
      · rcases m.htr 0 1 5 (by decide) (by decide) with h506 | h506
        · rcases m.htr 0 2 3 (by decide) (by decide) with h507 | h507
          · linarith only [h0, h1, h507, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h509 | h509
            · rcases m.htr 0 2 5 (by decide) (by decide) with h510 | h510
              · linarith only [h507, h510, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h512 | h512
                · rcases m.htr 0 3 5 (by decide) (by decide) with h513 | h513
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h514 | h514
                    · linarith only [h507, h509, h514, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                      · linarith only [h507, h516, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h506, h516, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                  · linarith only [h1, h506, h513, hlam]
                · linarith only [h1, h506, h509, h510, h512, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h521 | h521
              · linarith only [h507, h521, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h523 | h523
                · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h525 | h525
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h526 | h526
                      · linarith only [h0, h507, h526, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h526, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
                      · linarith only [h0, h507, h524, h529, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h1, h506, h529, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                  · linarith only [h1, h506, h524, hlam]
                · linarith only [h1, h505, h523, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h534 | h534
          · linarith only [h0, h1, h534, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h536 | h536
            · rcases m.htr 0 2 5 (by decide) (by decide) with h537 | h537
              · linarith only [h534, h537, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h539 | h539
                · rcases m.htr 0 3 5 (by decide) (by decide) with h540 | h540
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h541 | h541
                    · linarith only [h534, h536, h541, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
                      · linarith only [h0, h534, h543, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h543, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h546 | h546
                    · linarith only [h534, h536, h546, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                      · linarith only [h534, h548, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h548, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h536, h539, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h552 | h552
              · linarith only [h536, h552, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
                · rcases m.htr 0 3 5 (by decide) (by decide) with h555 | h555
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h556 | h556
                    · linarith only [h505, h506, h556, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
                      · linarith only [h534, h558, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h558, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
                    · linarith only [h1, h505, h555, h561, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h563 | h563
                      · linarith only [h0, h1, h555, h563, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h563, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h505, h554, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h567 | h567
        · rcases m.htr 0 2 3 (by decide) (by decide) with h568 | h568
          · linarith only [h0, h1, h568, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h570 | h570
            · linarith only [h505, h567, h568, h570, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h572 | h572
              · linarith only [h568, h572, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h574 | h574
                · rcases m.htr 0 3 5 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
                      · linarith only [h568, h577, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h567, h577, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                    · linarith only [h505, h567, h576, hlam]
                  · linarith only [h505, h567, h574, h575, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h582 | h582
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h583 | h583
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
                      · linarith only [h0, h568, h584, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1, h567, h584, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                    · linarith only [h1, h567, h574, h583, hlam]
                  · linarith only [h1, h567, h582, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h589 | h589
          · linarith only [h0, h1, h589, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h591 | h591
            · linarith only [h0, h505, h589, h591, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h593 | h593
              · linarith only [h589, h593, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h595 | h595
                · rcases m.htr 0 3 5 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h597 | h597
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                      · linarith only [h589, h598, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h598, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                      · linarith only [h0, h505, h597, h601, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1, h601, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
                    · linarith only [h595, h596, h604, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                      · linarith only [h0, h1, h596, h606, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h606, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h609 | h609
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h610 | h610
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h611 | h611
                      · linarith only [h0, h1, h595, h611, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h611, hc12, hlam, hphi, u2elo2]
                    · linarith only [h595, h609, h610, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h615 | h615
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h616 | h616
                      · linarith only [h0, h1, h609, h616, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h616, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                      · linarith only [h0, h1, h609, h619, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h619, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h622 | h622
    · rcases m.htr 0 1 4 (by decide) (by decide) with h623 | h623
      · rcases m.htr 0 1 5 (by decide) (by decide) with h624 | h624
        · linarith only [h0, h624, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h626 | h626
          · rcases m.htr 0 2 4 (by decide) (by decide) with h627 | h627
            · rcases m.htr 0 2 5 (by decide) (by decide) with h628 | h628
              · rcases m.htr 0 3 4 (by decide) (by decide) with h629 | h629
                · rcases m.htr 0 3 5 (by decide) (by decide) with h630 | h630
                  · linarith only [h0, h622, h630, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h632 | h632
                    · linarith only [h0, h622, h629, h632, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h636 | h636
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h637 | h637
                            · linarith only [h622, h624, h636, h637, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h622, h624, h629, h636, h637, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h628, h636, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h628, h635, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h634, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h643 | h643
                  · linarith only [h0, h623, h629, h643, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
                    · linarith only [h0, h623, h645, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h647 | h647
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h648 | h648
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h649 | h649
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h650 | h650
                            · linarith only [h622, h624, h629, h649, h650, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h652 | h652
                              · linarith only [h622, h624, h643, h649, h652, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h654 | h654
                                · linarith only [h623, h624, h629, h645, h649, h654, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
                                  · linarith only [h622, h629, h647, h656, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h658 | h658
                                    · linarith only [h624, h652, h658, hc01, hlam, hphi, ht12, u2elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h660 | h660
                                      · linarith only [h623, h624, h648, h649, h660, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h662 | h662
                                        · linarith only [h623, h624, h650, h654, h662, hc13, hc34, hlam, hphi]
                                        · rcases h3bigk with h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h622, h624, h647, h649, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u2elo1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h622, h624, h649, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u2elo1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h629, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h643, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h622, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h622, h624, h649, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p664_1, u2elo1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h650, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h652, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h626, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h647, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h656, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h658, hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h662, hc03, hc45, hlam, hphi, ht34, p664_1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h647, h662, hc23, hc45, hlam, hphi, ht34, p664_1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h662, hc23, hc45, hlam, hphi, ht34, p664_1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [hlam, p664_0]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h662, hlam, p664_1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            rcases p664_3 (m.d 0 3) (by simp) with h685 | h685
                                            · linarith only [h685, hlam, p664_0]
                                            · rcases p664_3 (m.d 1 3) (by simp) with h687 | h687
                                              · linarith only [h652, h687, hlam]
                                              · rcases p664_3 (m.d 2 3) (by simp) with h689 | h689
                                                · linarith only [h658, h689, hlam]
                                                · rcases p664_3 (m.d 3 4) (by simp) with h691 | h691
                                                  · linarith only [h662, h691, hlam]
                                                  · linarith only [h629, h691, hlam]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            rcases p664_3 (m.d 0 3) (by simp) with h694 | h694
                                            · linarith only [h643, h694, hlam]
                                            · linarith only [h622, h694, hlam]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            rcases p664_3 (m.d 0 3) (by simp) with h697 | h697
                                            · linarith only [h643, h697, hlam]
                                            · linarith only [h626, h697, hlam]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [h622, h629, h647, h662, hc23, hc45, hlam, hphi, ht34, p664_1]
                                          · have p664_0 := h664c.1
                                            have p664_1 := h664c.2.1
                                            have p664_2 := h664c.2.2.1
                                            have p664_3 := h664c.2.2.2
                                            linarith only [hlam, p664_0]
                          · linarith only [h628, h649, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h622, h647, h648, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h622, h647, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h705 | h705
                · rcases m.htr 0 3 5 (by decide) (by decide) with h706 | h706
                  · linarith only [h0, h622, h706, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h708 | h708
                    · linarith only [h0, h623, h628, h708, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h711 | h711
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h712 | h712
                          · linarith only [h0, h628, h712, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h622, h710, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h622, h710, h711, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h710, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h717 | h717
                  · linarith only [h0, h623, h705, h717, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h719 | h719
                    · linarith only [h0, h623, h628, h719, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h723 | h723
                          · linarith only [h0, h628, h723, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h622, h721, h723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h622, h721, h722, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h622, h721, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h623, h627, hlam]
          · linarith only [h0, h622, h626, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h730 | h730
        · linarith only [h0, h730, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h732 | h732
          · rcases m.htr 0 2 4 (by decide) (by decide) with h733 | h733
            · rcases m.htr 0 2 5 (by decide) (by decide) with h734 | h734
              · rcases m.htr 0 3 4 (by decide) (by decide) with h735 | h735
                · linarith only [h622, h623, h735, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h737 | h737
                  · linarith only [h0, h622, h737, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h742 | h742
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h743 | h743
                            · linarith only [h622, h623, h735, h741, h743, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h745 | h745
                              · linarith only [h622, h730, h737, h745, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h747 | h747
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h748 | h748
                                  · linarith only [h730, h743, h747, h748, hc01, hlam, hphi, ht12, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h750 | h750
                                    · linarith only [h622, h730, h740, h745, h750, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h752 | h752
                                      · linarith only [h733, h752, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                                        · rcases h3bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h622, h730, h740, h743, h747, hc23, hc34, hlam, hphi, p755_1]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h0, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u2elo1]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h735, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h737, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h622, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h0, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u2elo1]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h743, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h745, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h732, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h740, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h748, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h750, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            rcases p755_3 (m.d 0 3) (by simp) with h771 | h771
                                            · linarith only [h771, hlam, p755_0]
                                            · rcases p755_3 (m.d 1 3) (by simp) with h773 | h773
                                              · linarith only [h743, h773, hlam]
                                              · rcases p755_3 (m.d 2 3) (by simp) with h775 | h775
                                                · linarith only [h748, h775, hlam]
                                                · rcases p755_3 (m.d 3 4) (by simp) with h777 | h777
                                                  · rcases p755_3 (m.d 3 5) (by simp) with h778 | h778
                                                    · linarith only [h754, h778, hlam]
                                                    · linarith only [h737, h778, hlam]
                                                  · linarith only [h777, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            rcases p755_3 (m.d 0 3) (by simp) with h782 | h782
                                            · linarith only [h735, h782, hlam]
                                            · linarith only [h622, h782, hlam]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            rcases p755_3 (m.d 0 3) (by simp) with h785 | h785
                                            · linarith only [h735, h785, hlam]
                                            · linarith only [h732, h785, hlam]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h730, h745, hc01, hc34, hlam, hphi, ht12, ht23, p755_1]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            rcases p755_3 (m.d 0 3) (by simp) with h790 | h790
                                            · linarith only [h790, hlam, p755_0]
                                            · rcases p755_3 (m.d 1 3) (by simp) with h792 | h792
                                              · linarith only [h745, h792, hlam]
                                              · rcases p755_3 (m.d 2 3) (by simp) with h794 | h794
                                                · linarith only [h750, h794, hlam]
                                                · rcases p755_3 (m.d 3 4) (by simp) with h796 | h796
                                                  · rcases p755_3 (m.d 3 5) (by simp) with h797 | h797
                                                    · rcases h5bigk with h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [hlam, p798_0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h730, hlam, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [hlam, hphi, ht0b, ht5b, p798_1, u0elo4, u5ehi2]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h737, hlam, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h748, h752, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p798_1, u0elo4]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h742, hlam, hphi, ht01, ht0b, ht12, ht5b, p798_1, u2elo1, u5ehi0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [hlam, p798_0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h742, hlam, hphi, ht01, ht0b, ht12, ht5b, p798_1, u2elo1, u5ehi2]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h745, hlam, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h741, h747, h748, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p798_1, u2elo1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h734, hlam, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h742, hlam, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [hlam, p798_0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h750, hlam, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h752, hlam, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h622, h730, h740, h754, hc23, hc34, hlam, hphi, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h622, h730, h740, h754, hc23, hc34, hlam, hphi, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        rcases p798_3 (m.d 0 5) (by simp) with h816 | h816
                                                        · linarith only [h737, h816, hlam]
                                                        · linarith only [h734, h816, hlam]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [hlam, p798_0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h748, h752, h754, hc23, hc34, hlam, hphi, p798_1]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h739, hlam, p798_0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h747, hlam, p798_0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h739, hlam, hphi, ht0b, ht5b, p798_1, u0elo3, u5ehi2]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [h754, hlam, p798_0]
                                                      · have p798_0 := h798c.1
                                                        have p798_1 := h798c.2.1
                                                        have p798_2 := h798c.2.2.1
                                                        have p798_3 := h798c.2.2.2
                                                        linarith only [hlam, p798_0]
                                                    · linarith only [h797, hlam, p755_0]
                                                  · linarith only [h735, h796, hlam]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            rcases p755_3 (m.d 0 3) (by simp) with h828 | h828
                                            · linarith only [h737, h828, hlam]
                                            · linarith only [h622, h828, hlam]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            rcases p755_3 (m.d 0 3) (by simp) with h831 | h831
                                            · linarith only [h737, h831, hlam]
                                            · linarith only [h732, h831, hlam]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [h754, hlam, p755_0]
                                          · have p755_0 := h755c.1
                                            have p755_1 := h755c.2.1
                                            have p755_2 := h755c.2.2.1
                                            have p755_3 := h755c.2.2.2
                                            linarith only [hlam, p755_0]
                                        · linarith only [h735, h739, h754, hlam]
                                · linarith only [h622, h623, h740, h747, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h622, h740, h742, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h734, h741, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h740, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h841 | h841
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h842 | h842
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h843 | h843
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h844 | h844
                            · linarith only [h622, h623, h842, h844, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h846 | h846
                              · linarith only [h622, h623, h737, h739, h842, h846, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h848 | h848
                                · linarith only [h622, h623, h739, h841, h842, h848, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · linarith only [h622, h623, h841, h848, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h734, h843, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h622, h841, h842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h622, h841, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h854 | h854
                · linarith only [h622, h623, h854, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h856 | h856
                  · linarith only [h0, h622, h856, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h858 | h858
                    · linarith only [h733, h734, h858, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h860 | h860
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h861 | h861
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h862 | h862
                          · linarith only [h622, h623, h733, h734, h860, h862, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h622, h860, h862, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h622, h733, h860, h861, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h860, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h867 | h867
              · linarith only [h733, h867, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h869 | h869
                · linarith only [h0, h622, h733, h869, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h871 | h871
                  · linarith only [h0, h622, h733, h871, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h873 | h873
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h874 | h874
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h875 | h875
                        · linarith only [h0, h622, h733, h874, h875, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h622, h874, h875, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h874, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h880 | h880
                        · linarith only [h0, h622, h733, h879, h880, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h622, h879, h880, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h622, h879, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h622, h732, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h885 | h885
      · rcases m.htr 0 1 5 (by decide) (by decide) with h886 | h886
        · linarith only [h0, h886, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h888 | h888
          · rcases m.htr 0 2 4 (by decide) (by decide) with h889 | h889
            · rcases m.htr 0 2 5 (by decide) (by decide) with h890 | h890
              · rcases m.htr 0 3 4 (by decide) (by decide) with h891 | h891
                · rcases m.htr 0 3 5 (by decide) (by decide) with h892 | h892
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h893 | h893
                    · linarith only [h0, h885, h893, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h896 | h896
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h897 | h897
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h898 | h898
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h899 | h899
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h900 | h900
                                · linarith only [h885, h886, h893, h895, h899, h900, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h902 | h902
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h903 | h903
                                    · linarith only [h888, h903, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                    · linarith only [h892, h902, h903, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · linarith only [h885, h886, h895, h898, h899, h902, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h622, h892, h899, hlam]
                            · linarith only [h622, h891, h898, hlam]
                          · linarith only [h622, h892, h895, h897, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                        · linarith only [h622, h895, h896, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h885, h895, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h912 | h912
                    · linarith only [h0, h885, h912, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h915 | h915
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h916 | h916
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h917 | h917
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h918 | h918
                              · linarith only [h622, h885, h892, h914, h915, h918, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h920 | h920
                                · linarith only [h885, h912, h920, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h922 | h922
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h923 | h923
                                    · linarith only [h622, h888, h918, h923, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h925 | h925
                                      · linarith only [h622, h885, h915, h918, h920, h925, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h927 | h927
                                        · linarith only [h622, h885, h915, h918, h920, h922, h927, hlam]
                                        · linarith only [h622, h885, h915, h918, h922, h927, hc34, hc45, hlam, hphi]
                                  · linarith only [h622, h891, h918, h922, hc23, hc35, hlam, hphi]
                            · linarith only [h622, h885, h891, h917, hlam]
                          · linarith only [h0, h890, h916, hlam]
                        · linarith only [h0, h890, h915, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h914, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h622, h885, h891, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h936 | h936
                · rcases m.htr 0 3 5 (by decide) (by decide) with h937 | h937
                  · linarith only [h888, h890, h937, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h939 | h939
                    · linarith only [h0, h885, h939, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h941 | h941
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h942 | h942
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h943 | h943
                          · linarith only [h622, h888, h890, h943, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h885, h942, h943, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h622, h941, h942, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h885, h941, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h622, h885, h936, hlam]
            · linarith only [h622, h885, h888, h889, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h950 | h950
            · rcases m.htr 0 2 5 (by decide) (by decide) with h951 | h951
              · linarith only [h888, h951, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h953 | h953
                · rcases m.htr 0 3 5 (by decide) (by decide) with h954 | h954
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
                    · linarith only [h0, h885, h955, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h957 | h957
                      · linarith only [h0, h888, h957, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h885, h957, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h960 | h960
                    · linarith only [h0, h885, h951, h960, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h962 | h962
                      · linarith only [h0, h888, h962, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h885, h962, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h622, h885, h953, hlam]
            · linarith only [h0, h885, h950, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h967 | h967
        · linarith only [h0, h967, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h969 | h969
          · rcases m.htr 0 2 4 (by decide) (by decide) with h970 | h970
            · rcases m.htr 0 2 5 (by decide) (by decide) with h971 | h971
              · rcases m.htr 0 3 4 (by decide) (by decide) with h972 | h972
                · rcases m.htr 0 3 5 (by decide) (by decide) with h973 | h973
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h974 | h974
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h975 | h975
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h976 | h976
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h977 | h977
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h978 | h978
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h979 | h979
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h980 | h980
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h981 | h981
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h982 | h982
                                    · linarith only [h969, h982, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                    · linarith only [h973, h981, h982, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h985 | h985
                                    · linarith only [h0, h969, h972, h981, h985, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h987 | h987
                                      · linarith only [h0, h970, h987, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h989 | h989
                                        · linarith only [h0, h969, h972, h981, h987, h989, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                        · linarith only [h974, h981, h989, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h0, h885, h969, h972, h974, h980, hc01, hlam, hphi, ht12, u2elo1]
                              · linarith only [h622, h973, h979, hlam]
                            · linarith only [h622, h972, h978, hlam]
                          · linarith only [h0, h969, h973, h977, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                        · linarith only [h0, h969, h972, h974, h976, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                      · linarith only [h0, h969, h972, h974, h975, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h998 | h998
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1000 | h1000
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1001 | h1001
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1002 | h1002
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1003 | h1003
                                · linarith only [h1003, h885, h974, h999, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1005 | h1005
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1006 | h1006
                                    · linarith only [h1006, h969, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                    · linarith only [h1005, h1006, h973, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1009 | h1009
                                    · linarith only [h1005, h1009, h622, h972, h998, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1011 | h1011
                                      · linarith only [h1003, h1005, h1011, h622, h972, h998, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1013 | h1013
                                        · linarith only [h1003, h1013, h622, h885, h972, h998, hc01, hlam, hphi, ht12, u2elo1]
                                        · rcases h3bigk with h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h622, hlam, p1015_1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            rcases p1015_3 (m.d 0 3) (by simp) with h1018 | h1018
                                            · rcases p1015_3 (m.d 1 3) (by simp) with h1019 | h1019
                                              · rcases p1015_3 (m.d 2 3) (by simp) with h1020 | h1020
                                                · linarith only [h1020, h969, hlam]
                                                · rcases p1015_3 (m.d 3 4) (by simp) with h1022 | h1022
                                                  · linarith only [h1022, h972, hlam]
                                                  · linarith only [h1005, h1022, hlam]
                                              · linarith only [h1019, h998, hlam]
                                            · linarith only [h1018, h969, hlam]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1005, h622, h998, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1015_1, u2elo1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h622, h998, hlam, hphi, ht01, ht0b, ht12, ht5b, p1015_1, u2elo1, u5ehi3]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h622, h998, hc01, hlam, hphi, ht12, p1015_1, u2elo1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            rcases p1015_3 (m.d 0 3) (by simp) with h1031 | h1031
                                            · linarith only [h1031, h622, hlam]
                                            · linarith only [h1031, h969, hlam]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1005, h998, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1015_1, u2elo1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1005, h1013, h998, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1015_1, u2elo1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h969, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h998, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1005, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1009, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h972, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1001, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1013, h973, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1015_1, u0elo2]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1013, hlam, p1015_1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h973, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h1002, hlam, p1015_0]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h622, h973, h998, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1015_1, u2elo1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [h622, h973, h998, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1015_1, u2elo1]
                                          · have p1015_0 := h1015c.1
                                            have p1015_1 := h1015c.2.1
                                            have p1015_2 := h1015c.2.2.1
                                            have p1015_3 := h1015c.2.2.2
                                            linarith only [hlam, p1015_0]
                              · linarith only [h0, h1002, h622, h971, h973, hc01, hlam, hphi, ht12, u2elo1]
                            · linarith only [h1001, h622, h972, hlam]
                          · linarith only [h0, h1000, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h969, h973, h999, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                      · linarith only [h0, h998, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1056 | h1056
                    · linarith only [h1056, h972, h973, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1058 | h1058
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1059 | h1059
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1060 | h1060
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1061 | h1061
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1062 | h1062
                              · linarith only [h1058, h1062, h972, h973, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1064 | h1064
                                · linarith only [h1056, h1060, h1061, h1062, h1064, h885, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1066 | h1066
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1067 | h1067
                                    · linarith only [h1062, h1067, h969, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1069 | h1069
                                      · linarith only [h0, h1069, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1071 | h1071
                                        · linarith only [h1064, h1071, h885, hc01, hc34, hlam, hphi, ht12, ht23]
                                        · rcases h3bigk with h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h622, hlam, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1066, hc34, hlam, hphi, ht0b, ht45, ht5b, p1073_1, u0elo2]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1062, h1071, h622, hc34, hc45, hlam, hphi, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h973, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1062, h1071, hc03, hc45, hlam, hphi, ht34, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1062, h1066, h1071, hc34, hc45, hlam, hphi, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1062, h1071, hc34, hc45, hlam, hphi, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1062, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h969, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1058, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h0, h1067, h971, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1073_1, u2elo1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1067, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h972, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1061, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1066, hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [hlam, p1073_0]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1071, hlam, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1071, h972, hc34, hc45, hlam, hphi, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1071, h622, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [h1066, h1071, hc34, hc45, hlam, hphi, p1073_1]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            rcases p1073_3 (m.d 0 3) (by simp) with h1097 | h1097
                                            · linarith only [h1097, h973, hlam]
                                            · linarith only [h1097, h972, hlam]
                                          · have p1073_0 := h1073c.1
                                            have p1073_1 := h1073c.2.1
                                            have p1073_2 := h1073c.2.2.1
                                            have p1073_3 := h1073c.2.2.2
                                            linarith only [hlam, p1073_0]
                                  · linarith only [h1066, h972, h973, hc23, hc35, hlam, hphi]
                            · linarith only [h1061, h622, h972, hlam]
                          · linarith only [h0, h1060, h971, hlam]
                        · linarith only [h0, h1059, h971, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h1058, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1106 | h1106
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1107 | h1107
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1108 | h1108
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1109 | h1109
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1110 | h1110
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1111 | h1111
                            · linarith only [h1106, h1111, h972, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1113 | h1113
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1114 | h1114
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1115 | h1115
                                  · linarith only [h1111, h1115, h969, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1117 | h1117
                                    · linarith only [h0, h1115, h1117, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                    · linarith only [h1106, h1111, h1117, h622, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h1107, h1114, h885, h971, hc01, hlam, hphi, ht12, u2elo1]
                              · linarith only [h1106, h1113, h622, hlam]
                          · linarith only [h0, h1110, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h1109, h970, hlam]
                      · linarith only [h0, h1106, h1108, h970, h972, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                    · linarith only [h1106, h1107, h972, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1126 | h1126
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1127 | h1127
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1128 | h1128
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1129 | h1129
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1130 | h1130
                            · linarith only [h1127, h1130, h622, h972, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1132 | h1132
                              · linarith only [h1106, h1128, h1130, h1132, h622, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1134 | h1134
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1135 | h1135
                                  · linarith only [h1130, h1135, h622, hc01, hlam, hphi, ht12, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1137 | h1137
                                    · linarith only [h1132, h1135, h1137, h622, h970, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1139 | h1139
                                      · linarith only [h0, h1139, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1141 | h1141
                                        · rcases h3bigk with h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h622, hlam, p1142_1]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1132, h1141, h622, hc23, hc34, hlam, hphi, p1142_1]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h972, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1106, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1132, h1141, hc03, hc34, hlam, hphi, p1142_1]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1132, h1141, hc23, hc34, hlam, hphi, p1142_1]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1130, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1132, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h969, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1127, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1135, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1137, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            rcases p1142_3 (m.d 0 3) (by simp) with h1158 | h1158
                                            · linarith only [h1158, hlam, p1142_0]
                                            · rcases p1142_3 (m.d 1 3) (by simp) with h1160 | h1160
                                              · linarith only [h1130, h1160, hlam]
                                              · linarith only [h1160, h622, hlam]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1126, h1128, h1135, h1139, h622, h885, hc01, hc23, hc34, hlam, hphi, ht12, p1142_1, u2elo1]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            rcases p1142_3 (m.d 0 3) (by simp) with h1164 | h1164
                                            · linarith only [h1164, h972, hlam]
                                            · linarith only [h1164, h969, hlam]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1106, h1126, h1128, h1135, h1139, h622, h885, hc01, hc23, hc34, hlam, hphi, ht12, p1142_1, u2elo1]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            rcases p1142_3 (m.d 0 3) (by simp) with h1169 | h1169
                                            · linarith only [h1169, hlam, p1142_0]
                                            · rcases p1142_3 (m.d 1 3) (by simp) with h1171 | h1171
                                              · linarith only [h1132, h1171, hlam]
                                              · linarith only [h1171, h622, hlam]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1126, h1128, h1135, h1139, h622, h885, hc01, hc23, hc35, hlam, hphi, ht12, p1142_1, u2elo1]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            rcases p1142_3 (m.d 0 3) (by simp) with h1175 | h1175
                                            · linarith only [h1106, h1175, hlam]
                                            · linarith only [h1175, h969, hlam]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [h1141, hlam, p1142_0]
                                          · have p1142_0 := h1142c.1
                                            have p1142_1 := h1142c.2.1
                                            have p1142_2 := h1142c.2.2.1
                                            have p1142_3 := h1142c.2.2.2
                                            linarith only [hlam, p1142_0]
                                        · linarith only [h1126, h1128, h1141, h622, h885, h972, hc01, hlam, hphi, ht12, u2elo1]
                                · linarith only [h1126, h1134, h885, hlam]
                          · linarith only [h1126, h1128, h1129, h885, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                        · linarith only [h0, h1126, h1128, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                      · linarith only [h0, h1126, h1127, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1186 | h1186
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1187 | h1187
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1188 | h1188
                            · linarith only [h1185, h1188, h622, h972, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1190 | h1190
                              · linarith only [h1106, h1188, h1190, h622, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1192 | h1192
                                · linarith only [h1126, h1186, h1192, h885, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1194 | h1194
                                  · linarith only [h1194, h969, h972, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1196 | h1196
                                    · linarith only [h1190, h1196, h622, h969, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1198 | h1198
                                      · linarith only [h0, h1192, h1198, h885, h970, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1200 | h1200
                                        · linarith only [h1192, h1200, h885, hc01, hc34, hlam, hphi, ht12, ht23]
                                        · linarith only [h1188, h1200, h622, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h1187, h971, hlam]
                        · linarith only [h0, h1186, h971, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h1185, h969, h971, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1206 | h1206
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1207 | h1207
                  · linarith only [h1207, h969, h971, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1209 | h1209
                    · linarith only [h1209, h970, h971, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1211 | h1211
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1212 | h1212
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1213 | h1213
                          · linarith only [h1213, h971, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1213, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1211, h1212, h622, h970, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1211, h969, h971, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1218 | h1218
                  · linarith only [h1206, h1218, h970, h971, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1220 | h1220
                    · linarith only [h1220, h970, h971, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1222 | h1222
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1223 | h1223
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1224 | h1224
                          · linarith only [h1224, h971, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1224, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1222, h1223, h622, h970, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1222, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1229 | h1229
              · linarith only [h1229, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1231 | h1231
                · linarith only [h1231, h969, h970, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1233 | h1233
                  · linarith only [h1233, h969, h970, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1237 | h1237
                        · linarith only [h1237, h970, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1237, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1236, h969, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1241 | h1241
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1242 | h1242
                        · linarith only [h1242, h970, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1242, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1241, h969, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1246 | h1246
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1247 | h1247
              · linarith only [h1247, h969, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1249 | h1249
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1250 | h1250
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1251 | h1251
                    · linarith only [h1246, h1251, h969, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1253 | h1253
                      · linarith only [h1253, h969, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1253, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1256 | h1256
                    · linarith only [h1246, h1256, h969, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1258 | h1258
                      · linarith only [h1258, h969, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1258, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1246, h1249, h969, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1262 | h1262
              · linarith only [h1262, h969, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1264 | h1264
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1265 | h1265
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1266 | h1266
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1267 | h1267
                      · linarith only [h1267, h969, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1267, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1270 | h1270
                      · linarith only [h0, h1270, h969, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1270, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1273 | h1273
                    · linarith only [h1264, h1265, h1273, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1275 | h1275
                      · linarith only [h0, h1275, h969, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1275, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1278 | h1278
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1279 | h1279
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1280 | h1280
                      · linarith only [h0, h1280, h969, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1280, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1264, h1278, h1279, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1284 | h1284
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
                      · linarith only [h0, h1285, h969, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1285, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
                      · linarith only [h0, h1288, h969, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1288, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
