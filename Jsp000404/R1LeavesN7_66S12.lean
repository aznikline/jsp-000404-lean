import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_15_M_LI_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h5ehi := hb5.1
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
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h2, h61, h68, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                                · linarith only [h4, h6, h70, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                                · linarith only [h1, h59, h67, h70, hc23, hc35, hlam, hphi]
                            · linarith only [h4, h58, h6, h67, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h5, h6, h64, hc12, hlam, hphi, u2elo4]
                      · linarith only [h4, h6, h63, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
                  · linarith only [h5, h58, h6, h76, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h5, h6, h78, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                          · linarith only [h6, h82, hc02, hlam, hphi, u2elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                            · linarith only [h1, h58, h84, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                              · linarith only [h0, h78, h81, h86, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                                · linarith only [h1, h58, h80, h88, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                                  · linarith only [h0, h6, h76, h81, h88, h90, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                    · linarith only [h0, h78, h81, h92, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                                      · linarith only [h0, h6, h81, h88, h92, h94, hc23, hc34, hlam, hphi]
                                      · rcases h0bigk with h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h0, h81, h88, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1, u0elo0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          rcases p96_3 (m.d 0 1) (by simp) with h99 | h99
                                          · rcases p96_3 (m.d 0 2) (by simp) with h100 | h100
                                            · linarith only [h0, h100, hlam]
                                            · linarith only [h100, h4, hlam]
                                          · linarith only [h1, h99, hlam]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          rcases p96_3 (m.d 0 1) (by simp) with h104 | h104
                                          · rcases p96_3 (m.d 0 2) (by simp) with h105 | h105
                                            · linarith only [h0, h105, hlam]
                                            · linarith only [h105, h5, hlam]
                                          · linarith only [h104, h2, hlam]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [hlam, hphi, ht0b, ht5b, p96_1, u0elo0, u5ehi0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h0, hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h1, h6, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p96_1, u2elo4]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h1, h58, h6, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p96_1, u2elo4]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h6, hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h1, hlam, p96_1]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h4, hlam, p96_1]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h58, hlam, p96_1]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h76, hlam, p96_1]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h2, hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h5, hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h1, h5, h6, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p96_1, u2elo4]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h78, hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h3, hlam, p96_0]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [h0, h81, h88, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1, u0elo4]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          rcases p96_3 (m.d 0 1) (by simp) with h127 | h127
                                          · rcases p96_3 (m.d 0 2) (by simp) with h128 | h128
                                            · linarith only [h128, h6, hlam]
                                            · linarith only [h128, h4, hlam]
                                          · linarith only [h1, h127, hlam]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          rcases p96_3 (m.d 0 1) (by simp) with h132 | h132
                                          · rcases p96_3 (m.d 0 2) (by simp) with h133 | h133
                                            · linarith only [h133, h6, hlam]
                                            · linarith only [h133, h5, hlam]
                                          · linarith only [h132, h2, hlam]
                                        · have p96_0 := h96c.1
                                          have p96_1 := h96c.2.1
                                          have p96_2 := h96c.2.2.1
                                          have p96_3 := h96c.2.2.2
                                          linarith only [hlam, p96_0]
                        · linarith only [h5, h81, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h6, h80, hc12, hlam, hphi, u2elo4]
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
                            · linarith only [h1, h142, h146, h152, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                              · linarith only [h154, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h146, h147, h148, h154, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h147, h4, h5, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                        · linarith only [h159, h5, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                          · linarith only [h0, h161, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                            · linarith only [h0, h142, h158, h163, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                              · linarith only [h146, h165, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                                · linarith only [h142, h167, h4, h5, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                                  · linarith only [h0, h158, h169, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                                    · linarith only [h0, h146, h158, h171, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                    · linarith only [h0, h158, h171, h5, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h158, h4, h5, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h175 | h175
            · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
              · linarith only [h176, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
                · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h180 | h180
                    · linarith only [h175, h180, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
                      · linarith only [h182, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                          · linarith only [h0, h176, h185, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                              · linarith only [h180, h188, h2, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                                    · linarith only [h0, h180, h184, h192, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                                      · linarith only [h176, h190, h192, h194, hc02, hlam, hphi, u2elo3]
                                      · rcases h0bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h0, h184, hc24, hlam, hphi, ht0b, ht45, ht5b, p196_1, u0elo0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h179, hlam, hphi, ht0b, ht5b, p196_1, u0elo0, u5ehi3]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          rcases p196_3 (m.d 0 1) (by simp) with h200 | h200
                                          · rcases p196_3 (m.d 0 2) (by simp) with h201 | h201
                                            · linarith only [h0, h201, hlam]
                                            · linarith only [h175, h201, hlam]
                                          · linarith only [h2, h200, hlam]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [hlam, hphi, ht0b, ht5b, p196_1, u0elo0, u5ehi0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h0, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h4, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h176, h191, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p196_1, u2elo2]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h176, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h1, hlam, p196_1]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h0, h184, hc24, hlam, hphi, ht0b, ht45, ht5b, p196_1, u0elo2]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          rcases p196_3 (m.d 0 1) (by simp) with h214 | h214
                                          · rcases p196_3 (m.d 0 2) (by simp) with h215 | h215
                                            · linarith only [h215, h4, hlam]
                                            · linarith only [h175, h215, hlam]
                                          · linarith only [h2, h214, hlam]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h0, h176, h184, h190, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p196_1, u2elo2]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h2, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h175, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h178, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h180, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h3, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h0, h184, h190, hc34, hlam, hphi, ht0b, ht45, ht5b, p196_1, u0elo4]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [h179, hlam, p196_0]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          rcases p196_3 (m.d 0 1) (by simp) with h228 | h228
                                          · rcases p196_3 (m.d 0 2) (by simp) with h229 | h229
                                            · linarith only [h176, h229, hlam]
                                            · linarith only [h175, h229, hlam]
                                          · linarith only [h2, h228, hlam]
                                        · have p196_0 := h196c.1
                                          have p196_1 := h196c.2.1
                                          have p196_2 := h196c.2.2.1
                                          have p196_3 := h196c.2.2.2
                                          linarith only [hlam, p196_0]
                                  · linarith only [h179, h191, h4, hlam]
                                · linarith only [h178, h190, h4, hlam]
                            · linarith only [h175, h178, h182, h184, h187, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · linarith only [h175, h184, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h175, h238, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                      · linarith only [h240, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h242 | h242
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
                          · linarith only [h0, h176, h243, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h245 | h245
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                              · linarith only [h2, h238, h246, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                                  · linarith only [h179, h249, h4, hc02, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h251 | h251
                                    · linarith only [h0, h238, h242, h251, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h253 | h253
                                      · linarith only [h0, h176, h242, h248, h249, h251, h253, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                      · linarith only [h0, h242, h249, h253, h4, hc24, hc45, hlam, hphi]
                                · linarith only [h0, h178, h242, h248, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h178, h179, h245, hc13, hc35, hlam, hphi]
                        · linarith only [h175, h242, hc12, hlam, hphi, u2elo0]
                · linarith only [h175, h178, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h260 | h260
              · linarith only [h260, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
                · rcases m.htr 0 3 5 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                      · linarith only [h265, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                        · linarith only [h0, h175, h264, h267, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h269 | h269
                          · linarith only [h0, h260, h269, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                              · linarith only [h2, h272, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h262, h264, h267, h272, h4, hc12, hlam, hphi, u2elo2]
                            · linarith only [h262, h265, h271, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                      · linarith only [h276, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
                        · linarith only [h0, h175, h278, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                          · linarith only [h0, h260, h280, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h282 | h282
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h283 | h283
                              · linarith only [h1, h264, h282, h283, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                                    · linarith only [h0, h175, h264, h285, h287, hc12, hlam, hphi, u2elo2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                                      · linarith only [h2, h282, h289, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                                      · rcases h0bigk with h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          rcases p291_3 (m.d 0 1) (by simp) with h293 | h293
                                          · rcases p291_3 (m.d 0 2) (by simp) with h294 | h294
                                            · linarith only [h0, h294, hlam]
                                            · rcases p291_3 (m.d 0 3) (by simp) with h296 | h296
                                              · linarith only [h1, h296, hlam]
                                              · linarith only [h296, h4, hlam]
                                          · linarith only [h0, h293, hlam]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h1, h282, hc34, hlam, hphi, ht0b, ht45, ht5b, p291_1, u0elo0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          rcases p291_3 (m.d 0 1) (by simp) with h301 | h301
                                          · rcases p291_3 (m.d 0 2) (by simp) with h302 | h302
                                            · linarith only [h0, h302, hlam]
                                            · rcases p291_3 (m.d 0 3) (by simp) with h304 | h304
                                              · linarith only [h1, h304, hlam]
                                              · linarith only [h262, h304, hlam]
                                          · linarith only [h2, h301, hlam]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h3, hlam, hphi, ht0b, ht5b, p291_1, u0elo0, u5ehi1]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h0, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h4, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h175, hlam, p291_1]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h260, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h1, hlam, p291_1]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h0, h4, hc12, hlam, hphi, p291_1, u2elo2]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h0, h175, h4, hc12, hlam, hphi, p291_1, u2elo2]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p291_1, u2elo2, u5ehi1]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h2, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h0, h175, hc12, hlam, hphi, p291_1, u2elo3]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h262, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h264, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h3, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h0, h260, hc12, hlam, hphi, p291_1, u2elo4]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h263, hlam, p291_0]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [h0, h175, h263, h4, hc12, hlam, hphi, p291_1, u2elo2]
                                        · have p291_0 := h291c.1
                                          have p291_1 := h291c.2.1
                                          have p291_2 := h291c.2.2.1
                                          have p291_3 := h291c.2.2.2
                                          linarith only [hlam, p291_0]
                                  · linarith only [h263, h286, h4, hlam]
                                · linarith only [h263, h282, h285, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h262, h276, h282, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                    · linarith only [h262, h263, h332, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
                      · linarith only [h0, h262, h334, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h336 | h336
                        · linarith only [h0, h175, h336, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h338 | h338
                          · linarith only [h0, h260, h338, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                              · linarith only [h1, h175, h332, h340, h341, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h343 | h343
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h344 | h344
                                  · linarith only [h0, h263, h344, h4, hc12, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h346 | h346
                                    · linarith only [h0, h175, h332, h346, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h348 | h348
                                      · linarith only [h1, h340, h346, h348, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · rcases h0bigk with h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          rcases p350_3 (m.d 0 1) (by simp) with h352 | h352
                                          · rcases p350_3 (m.d 0 2) (by simp) with h353 | h353
                                            · linarith only [h0, h353, hlam]
                                            · rcases p350_3 (m.d 0 3) (by simp) with h355 | h355
                                              · linarith only [h1, h355, hlam]
                                              · linarith only [h355, h4, hlam]
                                          · linarith only [h0, h352, hlam]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h1, h340, hc34, hlam, hphi, ht0b, ht45, ht5b, p350_1, u0elo0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          rcases p350_3 (m.d 0 1) (by simp) with h360 | h360
                                          · rcases p350_3 (m.d 0 2) (by simp) with h361 | h361
                                            · linarith only [h0, h361, hlam]
                                            · rcases p350_3 (m.d 0 3) (by simp) with h363 | h363
                                              · linarith only [h1, h363, hlam]
                                              · linarith only [h262, h363, hlam]
                                          · linarith only [h2, h360, hlam]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [hlam, hphi, ht0b, ht5b, p350_1, u0elo0, u5ehi0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h0, hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h4, hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h175, hlam, p350_1]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h260, hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h1, hlam, p350_1]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h0, h344, h348, h4, hc12, hc45, hlam, hphi, ht23, ht34, p350_1]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h344, h348, h4, hc04, hc45, hlam, hphi, p350_1]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h263, hlam, p350_1]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h2, hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h0, h175, h343, h344, h348, hc12, hc45, hlam, hphi, ht23, ht34, p350_1]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h262, hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h332, hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h3, hlam, p350_0]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h0, h260, hc12, hlam, hphi, p350_1, u2elo4]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h1, h260, h340, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p350_1, u2elo4]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [h0, h175, h260, hc12, hlam, hphi, p350_1, u2elo4]
                                        · have p350_0 := h350c.1
                                          have p350_1 := h350c.2.1
                                          have p350_2 := h350c.2.2.1
                                          have p350_3 := h350c.2.2.2
                                          linarith only [hlam, p350_0]
                                · linarith only [h1, h340, h343, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h262, h334, h340, h4, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
                      · linarith only [h0, h392, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h394 | h394
                        · linarith only [h0, h175, h391, h394, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h396 | h396
                          · linarith only [h0, h396, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                            · linarith only [h262, h390, h398, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h400 | h400
                              · linarith only [h2, h400, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h175, h391, h394, h400, hc12, hlam, hphi, u2elo3]
                    · linarith only [h262, h390, h391, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                      · linarith only [h4, h405, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                        · linarith only [h0, h175, h407, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                          · linarith only [h0, h260, h409, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h411 | h411
                            · linarith only [h1, h262, h4, h411, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h413 | h413
                              · linarith only [h2, h413, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h175, h404, h407, h413, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                      · linarith only [h0, h4, h416, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                        · linarith only [h0, h175, h418, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                          · linarith only [h0, h260, h420, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h422 | h422
                            · linarith only [h1, h262, h4, h422, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h424 | h424
                              · linarith only [h2, h424, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h426 | h426
                                · linarith only [h0, h262, h4, h426, hc12, hlam, hphi, u2elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h428 | h428
                                  · linarith only [h390, h4, h428, hc02, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h430 | h430
                                    · linarith only [h1, h262, h404, h416, h430, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h432 | h432
                                      · linarith only [h175, h430, h432, hc02, hc34, hlam, hphi, ht23]
                                      · linarith only [h0, h4, h426, h432, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h435 | h435
          · rcases m.htr 0 2 4 (by decide) (by decide) with h436 | h436
            · rcases m.htr 0 2 5 (by decide) (by decide) with h437 | h437
              · linarith only [h0, h3, h437, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h439 | h439
                · rcases m.htr 0 3 5 (by decide) (by decide) with h440 | h440
                  · linarith only [h435, h437, h440, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                    · linarith only [h436, h437, h442, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                          · linarith only [h437, h446, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h3, h444, h446, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h436, h444, h445, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h435, h437, h444, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h451 | h451
                  · linarith only [h436, h437, h439, h451, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h453 | h453
                    · linarith only [h436, h437, h453, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h457 | h457
                          · linarith only [h0, h437, h457, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h3, h457, hc12, hlam, hphi, u2elo4]
                        · linarith only [h436, h437, h455, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h435, h437, h455, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h462 | h462
              · linarith only [h436, h462, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h464 | h464
                · linarith only [h435, h436, h464, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h466 | h466
                  · linarith only [h435, h436, h466, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h468 | h468
                    · linarith only [h2, h3, h468, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h471 | h471
                        · linarith only [h436, h471, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
                          · linarith only [h0, h2, h3, h436, h462, h473, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                          · linarith only [h2, h3, h470, h471, h473, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h435, h436, h470, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h477 | h477
            · rcases m.htr 0 2 5 (by decide) (by decide) with h478 | h478
              · linarith only [h435, h478, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h480 | h480
                · rcases m.htr 0 3 5 (by decide) (by decide) with h481 | h481
                  · linarith only [h1, h3, h481, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h483 | h483
                    · linarith only [h435, h477, h483, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h485 | h485
                      · linarith only [h435, h485, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h487 | h487
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h488 | h488
                          · linarith only [h0, h435, h478, h488, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                          · linarith only [h1, h3, h485, h487, h488, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h435, h477, h487, hc12, hlam, hphi, u2elo2]
                · linarith only [h435, h477, h480, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h493 | h493
              · linarith only [h435, h493, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h495 | h495
                · rcases m.htr 0 3 5 (by decide) (by decide) with h496 | h496
                  · linarith only [h1, h3, h496, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h498 | h498
                    · linarith only [h2, h3, h498, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
                      · linarith only [h435, h500, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h502 | h502
                        · linarith only [h0, h477, h502, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h504 | h504
                          · linarith only [h0, h3, h477, h493, h504, hc01, hlam, hphi, ht12, u2elo3]
                          · linarith only [h1, h3, h500, h504, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h507 | h507
                  · linarith only [h2, h3, h495, h507, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h509 | h509
                    · linarith only [h2, h3, h509, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
                      · linarith only [h435, h511, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h513 | h513
                        · linarith only [h0, h477, h513, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                          · linarith only [h0, h3, h435, h493, h515, hc01, hlam, hphi, ht12, u2elo2]
                          · linarith only [h1, h3, h511, h515, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h518 | h518
        · rcases m.htr 0 2 3 (by decide) (by decide) with h519 | h519
          · rcases m.htr 0 2 4 (by decide) (by decide) with h520 | h520
            · linarith only [h0, h2, h520, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h522 | h522
              · linarith only [h520, h522, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h524 | h524
                · linarith only [h2, h518, h519, h520, h524, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h526 | h526
                  · linarith only [h519, h520, h526, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h530 | h530
                        · linarith only [h0, h520, h530, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h2, h529, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h519, h522, h529, hc12, hlam, hphi, u2elo4]
                    · linarith only [h2, h518, h528, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h535 | h535
            · linarith only [h0, h2, h519, h535, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h537 | h537
              · linarith only [h519, h537, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h539 | h539
                · linarith only [h1, h2, h539, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h541 | h541
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
                      · linarith only [h0, h519, h543, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h545 | h545
                        · linarith only [h0, h2, h535, h537, h545, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1, h2, h541, h545, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                    · linarith only [h2, h518, h542, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h549 | h549
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
                      · linarith only [h519, h550, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h552 | h552
                        · linarith only [h0, h535, h552, hlam]
                        · linarith only [h1, h2, h550, h552, hc12, hlam, hphi, u2elo3]
                    · linarith only [h2, h518, h549, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h556 | h556
          · rcases m.htr 0 2 4 (by decide) (by decide) with h557 | h557
            · linarith only [h0, h2, h557, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h559 | h559
              · linarith only [h557, h559, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h561 | h561
                · linarith only [h0, h2, h556, h557, h561, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
                  · linarith only [h556, h557, h563, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h565 | h565
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h566 | h566
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                        · linarith only [h0, h557, h567, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h2, h566, h567, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h556, h566, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h571 | h571
                      · linarith only [h0, h2, h565, h571, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h556, h557, h571, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h574 | h574
            · linarith only [h0, h2, h556, h574, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h576 | h576
              · linarith only [h556, h576, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h578 | h578
                · linarith only [h1, h2, h578, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h580 | h580
                  · linarith only [h1, h518, h580, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h582 | h582
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h583 | h583
                      · linarith only [h556, h583, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h585 | h585
                        · linarith only [h1, h574, h582, h583, h585, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                        · linarith only [h1, h2, h583, h585, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                      · linarith only [h0, h2, h582, h588, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h590 | h590
                        · linarith only [h1, h2, h582, h588, h590, hc24, hc45, hlam, hphi]
                        · linarith only [h1, h2, h588, h590, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h593 | h593
      · rcases m.htr 0 1 5 (by decide) (by decide) with h594 | h594
        · rcases m.htr 0 2 3 (by decide) (by decide) with h595 | h595
          · linarith only [h0, h1, h595, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h597 | h597
            · rcases m.htr 0 2 5 (by decide) (by decide) with h598 | h598
              · linarith only [h595, h598, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h600 | h600
                · rcases m.htr 0 3 5 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                    · linarith only [h595, h597, h602, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                      · linarith only [h595, h604, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h594, h604, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                  · linarith only [h1, h594, h601, hlam]
                · linarith only [h1, h594, h597, h598, h600, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h609 | h609
              · linarith only [h595, h609, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h611 | h611
                · rcases m.htr 0 3 5 (by decide) (by decide) with h612 | h612
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h613 | h613
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h614 | h614
                      · linarith only [h0, h595, h614, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h614, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
                      · linarith only [h0, h595, h612, h617, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h1, h594, h617, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                  · linarith only [h1, h594, h612, hlam]
                · linarith only [h1, h593, h611, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h622 | h622
          · linarith only [h0, h1, h622, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h624 | h624
            · rcases m.htr 0 2 5 (by decide) (by decide) with h625 | h625
              · linarith only [h622, h625, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h627 | h627
                · rcases m.htr 0 3 5 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h629 | h629
                    · linarith only [h622, h624, h629, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h631 | h631
                      · linarith only [h622, h624, h631, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1, h631, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h634 | h634
                    · linarith only [h622, h624, h634, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h636 | h636
                      · linarith only [h622, h636, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h636, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h593, h627, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h640 | h640
              · linarith only [h624, h640, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h642 | h642
                · rcases m.htr 0 3 5 (by decide) (by decide) with h643 | h643
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h644 | h644
                    · linarith only [h593, h594, h644, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                      · linarith only [h622, h646, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h646, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                    · linarith only [h1, h593, h643, h649, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h651 | h651
                      · linarith only [h0, h1, h643, h651, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h651, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h593, h642, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h655 | h655
        · rcases m.htr 0 2 3 (by decide) (by decide) with h656 | h656
          · linarith only [h0, h1, h656, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h658 | h658
            · linarith only [h593, h655, h656, h658, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
              · linarith only [h656, h660, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h662 | h662
                · rcases m.htr 0 3 5 (by decide) (by decide) with h663 | h663
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h664 | h664
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
                      · linarith only [h656, h665, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h655, h665, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                    · linarith only [h593, h655, h664, hlam]
                  · linarith only [h593, h655, h662, h663, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h670 | h670
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h671 | h671
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
                      · linarith only [h0, h656, h672, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h672, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1, h655, h662, h671, hlam]
                  · linarith only [h1, h655, h670, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h677 | h677
          · linarith only [h0, h1, h677, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h679 | h679
            · linarith only [h0, h593, h677, h679, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h681 | h681
              · linarith only [h677, h681, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h683 | h683
                · rcases m.htr 0 3 5 (by decide) (by decide) with h684 | h684
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h685 | h685
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h686 | h686
                      · linarith only [h677, h686, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h686, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
                      · linarith only [h0, h593, h685, h689, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1, h689, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h692 | h692
                    · linarith only [h683, h684, h692, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h694 | h694
                      · linarith only [h0, h1, h684, h694, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1, h694, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h697 | h697
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h698 | h698
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h699 | h699
                      · linarith only [h0, h1, h683, h699, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h699, hc12, hlam, hphi, u2elo2]
                    · linarith only [h683, h697, h698, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h703 | h703
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                      · linarith only [h0, h1, h683, h704, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1, h704, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h707 | h707
                      · linarith only [h0, h1, h683, h703, h707, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1, h707, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h710 | h710
    · rcases m.htr 0 1 4 (by decide) (by decide) with h711 | h711
      · rcases m.htr 0 1 5 (by decide) (by decide) with h712 | h712
        · linarith only [h0, h712, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h714 | h714
          · rcases m.htr 0 2 4 (by decide) (by decide) with h715 | h715
            · rcases m.htr 0 2 5 (by decide) (by decide) with h716 | h716
              · rcases m.htr 0 3 4 (by decide) (by decide) with h717 | h717
                · rcases m.htr 0 3 5 (by decide) (by decide) with h718 | h718
                  · linarith only [h0, h710, h718, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h720 | h720
                    · linarith only [h0, h710, h717, h720, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h723 | h723
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
                            · linarith only [h710, h712, h724, h725, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h710, h712, h717, h724, h725, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h716, h724, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h716, h723, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h722, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h731 | h731
                  · linarith only [h0, h711, h717, h731, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
                    · linarith only [h0, h711, h733, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h736 | h736
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h738 | h738
                            · linarith only [h710, h712, h717, h737, h738, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h740 | h740
                              · linarith only [h711, h712, h733, h737, h740, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h742 | h742
                                · linarith only [h710, h717, h735, h742, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h744 | h744
                                  · linarith only [h710, h712, h731, h735, h737, h744, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                                    · linarith only [h712, h740, h746, hc01, hlam, hphi, ht12, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h748 | h748
                                      · linarith only [h711, h712, h735, h738, h740, h748, hc23, hc34, hlam, hphi]
                                      · rcases h0bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [hlam, p750_0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h0, hlam, p750_1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h710, h712, h735, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u2elo1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h711, h712, h735, h737, h738, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u2elo1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h712, hlam, p750_1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, p750_1, u2elo0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [hlam, p750_0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          rcases p750_3 (m.d 0 1) (by simp) with h758 | h758
                                          · linarith only [h0, h758, hlam]
                                          · linarith only [h710, h758, hlam]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          rcases p750_3 (m.d 0 1) (by simp) with h761 | h761
                                          · linarith only [h0, h761, hlam]
                                          · linarith only [h711, h761, hlam]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h0, h711, h712, h735, h738, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u2elo1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h710, hlam, p750_1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h714, hlam, p750_1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [hlam, p750_0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h717, hlam, p750_1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h731, hlam, p750_1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h711, hlam, p750_0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h715, hlam, p750_0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h0, h710, h711, h735, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u2elo1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [hlam, p750_0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h733, hlam, p750_0]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h710, h735, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1, u0elo4]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [h716, hlam, p750_1]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          rcases p750_3 (m.d 0 1) (by simp) with h777 | h777
                                          · linarith only [h712, h777, hlam]
                                          · linarith only [h710, h777, hlam]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          rcases p750_3 (m.d 0 1) (by simp) with h780 | h780
                                          · linarith only [h712, h780, hlam]
                                          · linarith only [h711, h780, hlam]
                                        · have p750_0 := h750c.1
                                          have p750_1 := h750c.2.1
                                          have p750_2 := h750c.2.2.1
                                          have p750_3 := h750c.2.2.2
                                          linarith only [hlam, p750_0]
                          · linarith only [h0, h737, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h710, h735, h736, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h710, h735, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h787 | h787
                · rcases m.htr 0 3 5 (by decide) (by decide) with h788 | h788
                  · linarith only [h0, h710, h788, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h790 | h790
                    · linarith only [h0, h711, h716, h790, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h792 | h792
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                          · linarith only [h0, h716, h794, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h710, h792, h794, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h710, h792, h793, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h792, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h799 | h799
                  · linarith only [h0, h711, h787, h799, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h801 | h801
                    · linarith only [h0, h711, h716, h801, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h803 | h803
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h804 | h804
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h805 | h805
                          · linarith only [h0, h716, h805, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h710, h803, h805, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h710, h803, h804, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h710, h803, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h711, h715, hlam]
          · linarith only [h0, h710, h714, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h812 | h812
        · linarith only [h0, h812, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h814 | h814
          · rcases m.htr 0 2 4 (by decide) (by decide) with h815 | h815
            · rcases m.htr 0 2 5 (by decide) (by decide) with h816 | h816
              · rcases m.htr 0 3 4 (by decide) (by decide) with h817 | h817
                · linarith only [h710, h711, h817, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h819 | h819
                  · linarith only [h0, h710, h819, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h821 | h821
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h822 | h822
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h824 | h824
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h825 | h825
                            · linarith only [h710, h711, h817, h823, h825, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h827 | h827
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h828 | h828
                                · linarith only [h812, h825, h827, h828, hc01, hlam, hphi, ht12, u2elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h830 | h830
                                  · linarith only [h710, h812, h819, h822, h823, h827, h830, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h832 | h832
                                    · linarith only [h815, h832, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h834 | h834
                                      · rcases h0bigk with h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [hlam, p835_0]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h0, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h812, h823, h827, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p835_1, u2elo1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h711, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h812, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p835_1, u2elo1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [hlam, p835_0]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          rcases p835_3 (m.d 0 1) (by simp) with h843 | h843
                                          · linarith only [h0, h843, hlam]
                                          · linarith only [h710, h843, hlam]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h0, h821, h828, h832, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p835_1, u2elo1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p835_1, u2elo1, u5ehi0]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h710, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h814, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [hlam, p835_0]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h817, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h819, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h710, h822, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p835_1, u0elo3]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h815, hlam, p835_0]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          rcases p835_3 (m.d 0 1) (by simp) with h855 | h855
                                          · linarith only [h711, h855, hlam]
                                          · linarith only [h710, h855, hlam]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [hlam, p835_0]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h710, h711, h812, h822, h823, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p835_1, u2elo1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h710, h822, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p835_1, u0elo4]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h816, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          rcases p835_3 (m.d 0 1) (by simp) with h862 | h862
                                          · linarith only [h812, h862, hlam]
                                          · linarith only [h710, h862, hlam]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [h821, hlam, p835_1]
                                        · have p835_0 := h835c.1
                                          have p835_1 := h835c.2.1
                                          have p835_2 := h835c.2.2.1
                                          have p835_3 := h835c.2.2.2
                                          linarith only [hlam, p835_0]
                                      · linarith only [h817, h821, h834, hlam]
                              · linarith only [h710, h711, h822, h827, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h710, h822, h824, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h816, h823, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h822, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h872 | h872
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h873 | h873
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h874 | h874
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h875 | h875
                            · linarith only [h710, h711, h817, h873, h875, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h877 | h877
                              · linarith only [h710, h711, h821, h872, h873, h877, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h710, h711, h872, h877, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h816, h874, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h710, h872, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h710, h872, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h883 | h883
                · linarith only [h710, h711, h883, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h885 | h885
                  · linarith only [h0, h710, h885, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h887 | h887
                    · linarith only [h815, h816, h887, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h890 | h890
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h891 | h891
                          · linarith only [h710, h711, h815, h816, h889, h891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h710, h889, h891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h710, h815, h889, h890, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h710, h889, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h896 | h896
              · linarith only [h815, h896, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h898 | h898
                · linarith only [h0, h710, h815, h898, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h900 | h900
                  · linarith only [h0, h710, h815, h900, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h903 | h903
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h904 | h904
                        · linarith only [h0, h815, h904, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h710, h903, h904, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h903, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
                        · linarith only [h0, h710, h815, h908, h909, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h710, h908, h909, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h710, h908, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h710, h814, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h914 | h914
      · rcases m.htr 0 1 5 (by decide) (by decide) with h915 | h915
        · linarith only [h0, h915, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h917 | h917
          · rcases m.htr 0 2 4 (by decide) (by decide) with h918 | h918
            · rcases m.htr 0 2 5 (by decide) (by decide) with h919 | h919
              · rcases m.htr 0 3 4 (by decide) (by decide) with h920 | h920
                · rcases m.htr 0 3 5 (by decide) (by decide) with h921 | h921
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h922 | h922
                    · linarith only [h0, h914, h922, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h924 | h924
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h925 | h925
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h928 | h928
                              · linarith only [h710, h914, h922, h924, h928, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h930 | h930
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h931 | h931
                                  · linarith only [h917, h931, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h921, h930, h931, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h710, h914, h924, h927, h930, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h710, h914, h920, h927, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h710, h914, h924, h925, h926, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h710, h914, h924, h925, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                      · linarith only [h0, h919, h924, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h939 | h939
                    · linarith only [h0, h914, h939, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h941 | h941
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h942 | h942
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h943 | h943
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h944 | h944
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h945 | h945
                              · linarith only [h710, h914, h939, h941, h945, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h947 | h947
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h948 | h948
                                  · linarith only [h917, h921, h948, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h950 | h950
                                    · linarith only [h914, h915, h942, h945, h950, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h952 | h952
                                      · linarith only [h915, h920, h945, h952, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                      · rcases h0bigk with h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h0, hlam, p954_1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h710, hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h710, h921, h952, hc04, hc45, hlam, hphi, p954_1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h915, hlam, p954_1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p954_1, u2elo1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h0, h710, h914, h942, h947, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p954_1, u2elo1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          rcases p954_3 (m.d 0 1) (by simp) with h963 | h963
                                          · linarith only [h0, h963, hlam]
                                          · linarith only [h914, h963, hlam]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p954_1, u2elo1, u5ehi0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h914, h942, h947, hc34, hlam, hphi, ht0b, ht45, ht5b, p954_1, u0elo2]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h917, hlam, p954_1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h914, h921, h942, h947, h952, hc34, hc45, hlam, hphi, p954_1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h921, hlam, p954_1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h914, hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h918, hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h920, hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h939, hlam, p954_0]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h914, h942, h947, hc34, hlam, hphi, ht0b, ht45, ht5b, p954_1, u0elo4]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h919, hlam, p954_1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [h0, h710, h914, h919, h942, h947, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p954_1, u2elo1]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          rcases p954_3 (m.d 0 1) (by simp) with h980 | h980
                                          · linarith only [h915, h980, hlam]
                                          · linarith only [h914, h980, hlam]
                                        · have p954_0 := h954c.1
                                          have p954_1 := h954c.2.1
                                          have p954_2 := h954c.2.2.1
                                          have p954_3 := h954c.2.2.2
                                          linarith only [hlam, p954_0]
                                · linarith only [h920, h921, h947, hc23, hc35, hlam, hphi]
                            · linarith only [h710, h920, h921, h944, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h710, h914, h919, h941, h942, h943, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h710, h941, h942, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h919, h941, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · linarith only [h710, h914, h920, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h990 | h990
                · rcases m.htr 0 3 5 (by decide) (by decide) with h991 | h991
                  · linarith only [h917, h919, h991, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h993 | h993
                    · linarith only [h0, h914, h993, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h995 | h995
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h996 | h996
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h997 | h997
                          · linarith only [h710, h917, h919, h997, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h914, h996, h997, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h710, h914, h995, h996, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                      · linarith only [h0, h914, h995, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h710, h914, h990, hlam]
            · linarith only [h0, h914, h918, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1004 | h1004
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1005 | h1005
              · linarith only [h1005, h917, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1007 | h1007
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1008 | h1008
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1009 | h1009
                    · linarith only [h0, h1009, h914, h917, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1011 | h1011
                      · linarith only [h0, h1011, h917, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1011, h914, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1014 | h1014
                    · linarith only [h0, h1005, h1014, h914, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1016 | h1016
                      · linarith only [h0, h1016, h917, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1016, h914, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1007, h710, h914, hlam]
            · linarith only [h0, h1004, h914, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1021 | h1021
        · linarith only [h0, h1021, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1023 | h1023
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1024 | h1024
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1025 | h1025
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1026 | h1026
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1027 | h1027
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1028 | h1028
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1029 | h1029
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1030 | h1030
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1031 | h1031
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1032 | h1032
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1033 | h1033
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1034 | h1034
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1035 | h1035
                                  · linarith only [h1023, h1035, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h1027, h1034, h1035, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1038 | h1038
                                  · linarith only [h0, h1023, h1038, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1040 | h1040
                                    · linarith only [h0, h1024, h1040, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1042 | h1042
                                      · linarith only [h1026, h1029, h1034, h1040, h1042, h710, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                      · linarith only [h1028, h1034, h1042, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h1028, h1033, h914, hlam]
                            · linarith only [h1026, h1032, h710, hlam]
                          · linarith only [h0, h1025, h1031, hlam]
                        · linarith only [h0, h1025, h1030, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h1025, h1029, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1050 | h1050
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1051 | h1051
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1052 | h1052
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1053 | h1053
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1054 | h1054
                              · linarith only [h1028, h1051, h1054, h914, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1056 | h1056
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1057 | h1057
                                  · linarith only [h1023, h1057, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · linarith only [h1027, h1050, h1056, h1057, h710, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1060 | h1060
                                  · linarith only [h1026, h1056, h1060, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1062 | h1062
                                    · linarith only [h1026, h1050, h1054, h1056, h1062, h710, h914, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1064 | h1064
                                      · linarith only [h1026, h1050, h1054, h1064, h710, h914, hc01, hlam, hphi, ht12, u2elo1]
                                      · rcases h0bigk with h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h0, hlam, p1066_1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h710, hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h914, hlam, p1066_1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1021, hlam, p1066_1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h0, h1027, h1056, h1064, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h0, h1026, h1056, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h0, h1026, h1028, h1056, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1050, h710, hc01, hlam, hphi, ht12, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1023, hlam, p1066_1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1026, h1050, h1056, h710, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1026, h1028, h1050, h1056, h710, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1054, h914, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1066_1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1024, hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1026, hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1028, hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h0, h1025, hc01, hlam, hphi, ht12, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1025, hlam, p1066_1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1027, hlam, p1066_0]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [h1027, h1050, h710, h914, hc01, hlam, hphi, ht12, p1066_1, u2elo1]
                                        · have p1066_0 := h1066c.1
                                          have p1066_1 := h1066c.2.1
                                          have p1066_2 := h1066c.2.2.1
                                          have p1066_3 := h1066c.2.2.2
                                          linarith only [hlam, p1066_0]
                            · linarith only [h1026, h1027, h1053, h710, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                          · linarith only [h1027, h1050, h1052, h710, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                        · linarith only [h0, h1024, h1051, hlam]
                      · linarith only [h0, h1025, h1050, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1096 | h1096
                    · linarith only [h1026, h1027, h1096, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1098 | h1098
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1100 | h1100
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1101 | h1101
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1102 | h1102
                              · linarith only [h1096, h1099, h1102, h914, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1104 | h1104
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1105 | h1105
                                  · linarith only [h1023, h1027, h1105, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1107 | h1107
                                    · linarith only [h1024, h1102, h1107, h914, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1109 | h1109
                                      · linarith only [h0, h1025, h1102, h1104, h1105, h1109, h914, hc01, hlam, hphi, ht12, u2elo1]
                                      · rcases h0bigk with h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, hlam, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h710, hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h914, hlam, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1021, hlam, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p1111_1, u2elo1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, h1023, h1104, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1111_1, u2elo1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, h914, hc01, hlam, hphi, ht12, p1111_1, u2elo1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1111_1, u2elo1, u5ehi0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1027, hc01, hc35, hlam, hphi, ht12, ht23, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1023, hlam, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1098, h710, h914, hc01, hlam, hphi, ht12, p1111_1, u2elo1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1027, hlam, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1102, h914, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1024, hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1026, hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1096, hlam, p1111_0]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, h1025, hc01, hlam, hphi, ht12, p1111_1, u2elo1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h1025, hlam, p1111_1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, h1025, h710, hc01, hlam, hphi, ht12, p1111_1, u2elo1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [h0, h1025, h914, hc01, hlam, hphi, ht12, p1111_1, u2elo1]
                                        · have p1111_0 := h1111c.1
                                          have p1111_1 := h1111c.2.1
                                          have p1111_2 := h1111c.2.2.1
                                          have p1111_3 := h1111c.2.2.2
                                          linarith only [hlam, p1111_0]
                                · linarith only [h1026, h1027, h1104, hc23, hc35, hlam, hphi]
                            · linarith only [h1026, h1027, h1101, hc13, hc35, hlam, hphi]
                          · linarith only [h0, h1025, h1100, hlam]
                        · linarith only [h0, h1025, h1099, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · linarith only [h0, h1098, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1142 | h1142
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1143 | h1143
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1144 | h1144
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1145 | h1145
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1146 | h1146
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1147 | h1147
                            · linarith only [h1026, h1142, h1147, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1149 | h1149
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1150 | h1150
                                · linarith only [h1023, h1147, h1150, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1152 | h1152
                                  · linarith only [h0, h1024, h1150, h1152, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                  · linarith only [h1142, h1147, h1152, h710, hc23, hc34, hlam, hphi]
                              · linarith only [h1143, h1149, h914, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h0, h1024, h1026, h1142, h1146, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                        · linarith only [h0, h1024, h1145, hlam]
                      · linarith only [h0, h1024, h1026, h1142, h1144, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                    · linarith only [h1026, h1142, h1143, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1160 | h1160
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1161 | h1161
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1162 | h1162
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1163 | h1163
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1164 | h1164
                            · linarith only [h1026, h1161, h1164, h710, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1166 | h1166
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1167 | h1167
                                · linarith only [h1164, h1167, h710, hc01, hlam, hphi, ht12, u2elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1169 | h1169
                                  · linarith only [h1024, h1142, h1167, h1169, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1171 | h1171
                                    · linarith only [h0, h1024, h1171, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1173 | h1173
                                      · rcases h0bigk with h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [hlam, p1174_0]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h0, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h710, hlam, p1174_0]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h914, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1021, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p1174_1, u2elo1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [hlam, p1174_0]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h0, h710, hc01, hlam, hphi, ht12, p1174_1, u2elo1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h0, h1160, h1167, h1171, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1174_1, u2elo1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p1174_1, u2elo1, u5ehi0]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1164, h710, hc01, hc34, hlam, hphi, ht12, ht23, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1023, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [hlam, p1174_0]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1026, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1142, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1162, h914, hc01, hlam, hphi, ht12, p1174_1, u2elo1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1024, hlam, p1174_0]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1162, h710, h914, hc01, hlam, hphi, ht12, p1174_1, u2elo1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [hlam, p1174_0]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1025, h1162, h914, hlam, hphi, ht01, ht0b, ht12, ht5b, p1174_1, u2elo1, u5ehi2]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h0, h1025, hc01, hlam, hphi, ht12, p1174_1, u2elo1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1025, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h0, h1025, h710, hc01, hlam, hphi, ht12, p1174_1, u2elo1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [h1160, hlam, p1174_1]
                                        · have p1174_0 := h1174c.1
                                          have p1174_1 := h1174c.2.1
                                          have p1174_2 := h1174c.2.2.1
                                          have p1174_3 := h1174c.2.2.2
                                          linarith only [hlam, p1174_0]
                                      · linarith only [h1160, h1162, h1164, h1173, h914, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h1160, h1166, h914, hlam]
                          · linarith only [h1160, h1162, h1163, h914, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                        · linarith only [h0, h1024, h1162, hlam]
                      · linarith only [h0, h1024, h1160, h1161, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1206 | h1206
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1207 | h1207
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1208 | h1208
                            · linarith only [h1026, h1205, h1208, h710, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1210 | h1210
                              · linarith only [h1160, h1206, h1210, h914, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1212 | h1212
                                · linarith only [h1023, h1142, h1208, h1212, hc13, hc35, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1214 | h1214
                                  · linarith only [h1023, h1214, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                                    · linarith only [h0, h1024, h1208, h1210, h1216, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1218 | h1218
                                      · linarith only [h1208, h1210, h1218, h710, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · linarith only [h1208, h1218, h710, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h1025, h1207, hlam]
                        · linarith only [h0, h1024, h1025, h1206, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                      · linarith only [h0, h1205, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1224 | h1224
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1225 | h1225
                  · linarith only [h1023, h1025, h1225, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1227 | h1227
                    · linarith only [h1023, h1025, h1224, h1227, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1229 | h1229
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1230 | h1230
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1231 | h1231
                          · linarith only [h1025, h1231, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1231, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1024, h1025, h1229, h1230, h710, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1023, h1025, h1229, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1236 | h1236
                  · linarith only [h1024, h1025, h1224, h1236, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1238 | h1238
                    · linarith only [h1024, h1025, h1238, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1240 | h1240
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1241 | h1241
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1242 | h1242
                          · linarith only [h1025, h1242, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1242, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1024, h1025, h1240, h1241, h710, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1023, h1025, h1240, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1247 | h1247
              · linarith only [h1024, h1247, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1249 | h1249
                · linarith only [h1023, h1024, h1249, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1251 | h1251
                  · linarith only [h1023, h1024, h1251, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1253 | h1253
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1254 | h1254
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1255 | h1255
                        · linarith only [h1024, h1255, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1255, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1023, h1254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1259 | h1259
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1260 | h1260
                        · linarith only [h1024, h1260, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1260, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1023, h1259, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1264 | h1264
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1265 | h1265
              · linarith only [h1023, h1265, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1267 | h1267
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1268 | h1268
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1269 | h1269
                    · linarith only [h1023, h1264, h1269, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1271 | h1271
                      · linarith only [h1023, h1271, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1271, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1274 | h1274
                    · linarith only [h1023, h1264, h1274, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1276 | h1276
                      · linarith only [h1023, h1276, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1276, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1023, h1264, h1267, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1280 | h1280
              · linarith only [h1264, h1280, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1282 | h1282
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1283 | h1283
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1284 | h1284
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
                      · linarith only [h1023, h1285, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1285, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
                      · linarith only [h0, h1023, h1288, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1288, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1291 | h1291
                    · linarith only [h1282, h1283, h1291, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1293 | h1293
                      · linarith only [h0, h1023, h1293, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1293, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1296 | h1296
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1297 | h1297
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1298 | h1298
                      · linarith only [h0, h1023, h1298, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1298, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1282, h1296, h1297, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1302 | h1302
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1303 | h1303
                      · linarith only [h0, h1023, h1303, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1303, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1306 | h1306
                      · linarith only [h0, h1023, h1306, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1306, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
