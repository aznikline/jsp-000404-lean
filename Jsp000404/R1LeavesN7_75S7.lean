import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_M_LI_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h1, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · linarith only [h0, h4, h6, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                    · linarith only [h1, h12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · linarith only [h0, h12, h4, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h6, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                    · linarith only [h19, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h1, h21, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                        · linarith only [h23, h4, h6, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                          · rcases h0bigk with h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h23, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0, u3ehi0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h18, hc45, hlam, hphi, ht01, ht0b, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, h16, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0, u3ehi1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo1, u3ehi1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, h23, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, h1, h16, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0, u3ehi1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h4, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h6, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h16, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h2, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h5, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo3, u3ehi1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, h16, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo3, u3ehi1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u0elo4, u3ehi1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h18, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                          · linarith only [h1, h25, h6, hc45, hlam, hphi, ht34, u3ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                    · linarith only [h1, h53, h6, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                      · linarith only [h1, h16, h55, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                        · linarith only [h0, h1, h4, h57, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                          · linarith only [h1, h18, h59, h6, hc34, hlam, hphi, u3ehi1]
                          · linarith only [h1, h59, h6, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h62 | h62
              · linarith only [h4, h5, h62, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
                · linarith only [h62, h64, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                    · linarith only [h62, h67, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                      · linarith only [h1, h64, h69, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                        · linarith only [h4, h5, h62, h71, hlam]
                        · linarith only [h4, h5, h71, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h4, h5, h66, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                    · linarith only [h1, h79, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h1, h76, h79, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                    · linarith only [h1, h82, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · linarith only [h1, h76, h82, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                · linarith only [h76, h77, hc35, hlam, hphi, u3ehi3]
              · linarith only [h4, h75, h76, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                    · linarith only [h1, h90, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · linarith only [h87, h90, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                    · linarith only [h1, h93, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                    · linarith only [h1, h87, h93, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                · linarith only [h87, h88, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h97 | h97
                · linarith only [h87, h97, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                    · linarith only [h100, h87, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                      · linarith only [h1, h102, h97, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                          · rcases h0bigk with h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              rcases p106_3 (m.d 0 1) (by simp) with h108 | h108
                              · rcases p106_3 (m.d 0 2) (by simp) with h109 | h109
                                · linarith only [h0, h109, hlam]
                                · rcases p106_3 (m.d 0 3) (by simp) with h111 | h111
                                  · linarith only [h1, h111, hlam]
                                  · linarith only [h111, h4, hlam]
                              · linarith only [h0, h108, hlam]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p106_1, u1elo0, u3ehi1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, h97, h99, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p106_1, u1elo0, u3ehi1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, h97, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p106_1, u1elo0, u3ehi1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h0, hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h4, hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h75, hlam, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, h97, hlam, hphi, ht0b, ht34, ht45, ht5b, p106_1, u0elo1, u3ehi1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, hlam, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h104, h105, h97, hc02, hc24, hlam, hphi, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h87, hlam, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h97, hlam, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h2, hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h0, h104, h87, hc12, hc23, hlam, hphi, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, h104, h87, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p106_1, u3ehi1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, h104, h87, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p106_1, u3ehi1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h3, hlam, p106_0]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h0, h104, h87, h99, hc12, hc23, hlam, hphi, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p106_1, u1elo0, u3ehi1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [h99, hlam, p106_1]
                            · have p106_0 := h106c.1
                              have p106_1 := h106c.2.1
                              have p106_2 := h106c.2.2.1
                              have p106_3 := h106c.2.2.2
                              linarith only [hlam, p106_0]
                          · linarith only [h105, h87, h99, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                          · rcases h0bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              rcases p140_3 (m.d 0 1) (by simp) with h142 | h142
                              · rcases p140_3 (m.d 0 2) (by simp) with h143 | h143
                                · linarith only [h0, h143, hlam]
                                · rcases p140_3 (m.d 0 3) (by simp) with h145 | h145
                                  · linarith only [h1, h145, hlam]
                                  · linarith only [h145, h4, hlam]
                              · linarith only [h0, h142, hlam]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h1, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p140_1, u1elo0, u3ehi1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h99, hc45, hlam, hphi, ht01, ht0b, ht5b, p140_1, u1elo0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h1, h97, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p140_1, u1elo0, u3ehi1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h0, hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h4, hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h75, hlam, p140_1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h1, h97, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1, u0elo1, u3ehi1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h1, hlam, p140_1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h97, hc02, hc35, hlam, hphi, ht23, p140_1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h87, hlam, p140_1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h97, hlam, p140_1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h2, hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              rcases p140_3 (m.d 0 1) (by simp) with h163 | h163
                              · rcases p140_3 (m.d 0 2) (by simp) with h164 | h164
                                · linarith only [h164, h75, hlam]
                                · rcases p140_3 (m.d 0 3) (by simp) with h166 | h166
                                  · linarith only [h166, h87, hlam]
                                  · linarith only [h166, h4, hlam]
                              · linarith only [h0, h163, hlam]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1, u0elo3, u3ehi0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h1, h2, h97, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p140_1, u1elo0, u3ehi1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h3, hlam, p140_0]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              rcases p140_3 (m.d 0 1) (by simp) with h174 | h174
                              · rcases p140_3 (m.d 0 2) (by simp) with h175 | h175
                                · linarith only [h175, hlam, p140_0]
                                · rcases p140_3 (m.d 0 3) (by simp) with h177 | h177
                                  · linarith only [h177, h97, hlam]
                                  · linarith only [h177, h4, hlam]
                              · linarith only [h0, h174, hlam]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1, u0elo4, u3ehi1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [h99, hlam, p140_1]
                            · have p140_0 := h140c.1
                              have p140_1 := h140c.2.1
                              have p140_2 := h140c.2.2.1
                              have p140_3 := h140c.2.2.2
                              linarith only [hlam, p140_0]
                          · linarith only [h104, h139, hc45, hlam, hphi, ht34, u3ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                    · linarith only [h1, h185, h87, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                      · linarith only [h1, h187, h87, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h189 | h189
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h190 | h190
                          · linarith only [h0, h189, h190, h75, h99, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h190, h87, hc45, hlam, hphi, ht34, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                          · linarith only [h1, h193, h87, h99, hc34, hlam, hphi, u3ehi1]
                          · linarith only [h189, h193, hc45, hlam, hphi, ht34, u3ehi2]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h198 | h198
      · rcases m.htr 0 1 5 (by decide) (by decide) with h199 | h199
        · rcases m.htr 0 2 3 (by decide) (by decide) with h200 | h200
          · linarith only [h0, h1, h200, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h202 | h202
            · rcases m.htr 0 3 4 (by decide) (by decide) with h203 | h203
              · rcases m.htr 0 3 5 (by decide) (by decide) with h204 | h204
                · rcases m.htr 0 4 5 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                    · linarith only [h1, h198, h206, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h1, h203, h206, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h209 | h209
                    · linarith only [h1, h198, h209, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h1, h198, h202, h203, h209, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h203, h204, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1, h202, h203, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 3 5 (by decide) (by decide) with h215 | h215
                · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h217 | h217
                    · linarith only [h1, h198, h217, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h1, h214, h217, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
                    · linarith only [h1, h198, h220, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h1, h198, h214, h216, h220, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                · linarith only [h214, h215, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h198, h214, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h225 | h225
          · linarith only [h0, h1, h225, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h227 | h227
            · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
              · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
                · rcases m.htr 0 4 5 (by decide) (by decide) with h230 | h230
                  · linarith only [h0, h199, h227, h230, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                    · linarith only [h1, h198, h232, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h1, h228, h232, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h228, h229, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1, h227, h228, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h237 | h237
              · rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
                · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
                  · linarith only [h198, h199, h239, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                    · linarith only [h198, h199, h241, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi3]
                    · linarith only [h237, h241, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · linarith only [h237, h238, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h198, h237, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h246 | h246
        · rcases m.htr 0 2 3 (by decide) (by decide) with h247 | h247
          · linarith only [h0, h198, h247, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h249 | h249
            · linarith only [h0, h198, h249, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 3 5 (by decide) (by decide) with h252 | h252
                · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h254 | h254
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h255 | h255
                      · linarith only [h198, h246, h254, h255, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                      · linarith only [h0, h198, h254, h255, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h251, h254, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h198, h246, h253, hlam]
                · linarith only [h251, h252, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
                · linarith only [h251, h261, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1, h246, h261, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h264 | h264
          · linarith only [h0, h198, h264, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h266 | h266
            · linarith only [h0, h198, h266, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h268 | h268
              · rcases m.htr 0 3 5 (by decide) (by decide) with h269 | h269
                · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h272 | h272
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h273 | h273
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                          · rcases h0bigk with h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h198, h271, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p275_1, u1elo2]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h1, hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h198, hlam, p275_1]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h246, hlam, p275_1]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h264, hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h266, hlam, p275_1]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, h246, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p275_1, u0elo1]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p275_1, u0elo2]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              rcases p275_3 (m.d 0 1) (by simp) with h287 | h287
                              · linarith only [h1, h287, hlam]
                              · linarith only [h0, h287, hlam]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, h1, h246, h270, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p275_1, u1elo2]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, h1, h246, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p275_1, u1elo2]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p275_1, u0elo3]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              rcases p275_3 (m.d 0 1) (by simp) with h294 | h294
                              · linarith only [h198, h294, hlam]
                              · linarith only [h0, h294, hlam]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h268, hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, h198, h246, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p275_1, u1elo2]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p275_1, u0elo4]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              rcases p275_3 (m.d 0 1) (by simp) with h301 | h301
                              · linarith only [h246, h301, hlam]
                              · linarith only [h0, h301, hlam]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h269, hlam, p275_0]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [h270, hlam, p275_1]
                            · have p275_0 := h275c.1
                              have p275_1 := h275c.2.1
                              have p275_2 := h275c.2.2.1
                              have p275_3 := h275c.2.2.2
                              linarith only [hlam, p275_0]
                          · linarith only [h198, h270, h271, h274, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                        · linarith only [h264, h268, h273, hlam]
                      · linarith only [h0, h1, h272, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h269, h271, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h312 | h312
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h313 | h313
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h314 | h314
                          · linarith only [h268, h270, h314, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases h0bigk with h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, h198, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p316_1, u1elo3]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h1, hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h198, hlam, p316_1]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h246, hlam, p316_1]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h264, hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h266, hlam, p316_1]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, h198, h270, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p316_1, u0elo1]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p316_1, u1elo2]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              rcases p316_3 (m.d 0 1) (by simp) with h328 | h328
                              · linarith only [h1, h328, hlam]
                              · linarith only [h0, h328, hlam]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, h1, h198, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p316_1, u1elo2]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, h1, h198, h270, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p316_1, u1elo2]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p316_1, u0elo3]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h270, hc02, hc45, hlam, hphi, ht23, ht34, p316_1]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h268, hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h270, hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, h246, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p316_1, u1elo4]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              rcases p316_3 (m.d 0 1) (by simp) with h340 | h340
                              · linarith only [h246, h340, hlam]
                              · linarith only [h0, h340, hlam]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h269, hlam, p316_0]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [h0, h1, h198, h269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p316_1, u1elo2]
                            · have p316_0 := h316c.1
                              have p316_1 := h316c.2.1
                              have p316_2 := h316c.2.2.1
                              have p316_3 := h316c.2.2.2
                              linarith only [hlam, p316_0]
                        · linarith only [h264, h269, h313, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h269, h312, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h1, h268, h269, h311, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                · linarith only [h268, h269, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h350 | h350
                · linarith only [h268, h350, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
                    · linarith only [h268, h353, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · linarith only [h0, h1, h353, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                    · linarith only [h0, h1, h268, h356, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h356, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h359 | h359
    · linarith only [h0, h359, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h361 | h361
      · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
        · rcases m.htr 0 2 3 (by decide) (by decide) with h363 | h363
          · rcases m.htr 0 2 4 (by decide) (by decide) with h364 | h364
            · rcases m.htr 0 3 4 (by decide) (by decide) with h365 | h365
              · rcases m.htr 0 3 5 (by decide) (by decide) with h366 | h366
                · rcases m.htr 0 4 5 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                    · linarith only [h0, h361, h368, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h359, h363, h365, h368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                    · linarith only [h0, h361, h371, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h359, h361, h365, h371, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h365, h366, hc35, hlam, hphi, u3ehi3]
              · linarith only [h359, h361, h365, hlam]
            · linarith only [h0, h361, h364, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h377 | h377
            · rcases m.htr 0 3 4 (by decide) (by decide) with h378 | h378
              · rcases m.htr 0 3 5 (by decide) (by decide) with h379 | h379
                · rcases m.htr 0 4 5 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h381 | h381
                    · linarith only [h359, h361, h381, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h359, h378, h381, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                    · linarith only [h0, h361, h384, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h359, h378, h380, h384, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h378, h379, hc35, hlam, hphi, u3ehi3]
              · linarith only [h359, h361, h378, hlam]
            · linarith only [h0, h361, h377, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h390 | h390
          · rcases m.htr 0 2 4 (by decide) (by decide) with h391 | h391
            · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                  · linarith only [h361, h362, h394, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
                    · linarith only [h0, h361, h396, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h359, h390, h392, h396, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h392, h393, hc35, hlam, hphi, u3ehi3]
              · linarith only [h359, h361, h392, hlam]
            · linarith only [h0, h361, h391, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h402 | h402
            · rcases m.htr 0 3 4 (by decide) (by decide) with h403 | h403
              · rcases m.htr 0 3 5 (by decide) (by decide) with h404 | h404
                · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
                  · linarith only [h361, h362, h405, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                    · linarith only [h359, h361, h407, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h359, h403, h407, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h403, h404, hc35, hlam, hphi, u3ehi3]
              · linarith only [h359, h361, h403, hlam]
            · linarith only [h0, h361, h402, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h413 | h413
        · rcases m.htr 0 2 3 (by decide) (by decide) with h414 | h414
          · rcases m.htr 0 2 4 (by decide) (by decide) with h415 | h415
            · rcases m.htr 0 3 4 (by decide) (by decide) with h416 | h416
              · rcases m.htr 0 3 5 (by decide) (by decide) with h417 | h417
                · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h420 | h420
                      · linarith only [h361, h413, h419, h420, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                      · linarith only [h359, h416, h420, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h359, h416, h419, hlam]
                  · linarith only [h361, h413, h418, hlam]
                · linarith only [h416, h417, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h426 | h426
                · linarith only [h416, h426, hc34, hlam, hphi, u3ehi4]
                · linarith only [h359, h413, h426, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
              · linarith only [h414, h415, h429, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h431 | h431
                · linarith only [h429, h431, hc34, hlam, hphi, u3ehi4]
                · linarith only [h359, h413, h431, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h434 | h434
            · rcases m.htr 0 3 4 (by decide) (by decide) with h435 | h435
              · rcases m.htr 0 3 5 (by decide) (by decide) with h436 | h436
                · rcases m.htr 0 4 5 (by decide) (by decide) with h437 | h437
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h438 | h438
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h439 | h439
                      · linarith only [h361, h413, h438, h439, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                      · linarith only [h359, h435, h439, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h359, h413, h435, h436, h438, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                  · linarith only [h361, h413, h437, hlam]
                · linarith only [h435, h436, hc35, hlam, hphi, u3ehi3]
              · linarith only [h414, h434, h435, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h446 | h446
              · rcases m.htr 0 3 5 (by decide) (by decide) with h447 | h447
                · rcases m.htr 0 4 5 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h449 | h449
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h450 | h450
                      · linarith only [h0, h413, h450, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                      · linarith only [h359, h446, h450, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h359, h446, h449, hlam]
                  · linarith only [h0, h413, h434, h448, hlam]
                · linarith only [h446, h447, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h456 | h456
                · linarith only [h446, h456, hc34, hlam, hphi, u3ehi4]
                · linarith only [h359, h413, h456, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h459 | h459
          · rcases m.htr 0 2 4 (by decide) (by decide) with h460 | h460
            · rcases m.htr 0 3 4 (by decide) (by decide) with h461 | h461
              · rcases m.htr 0 3 5 (by decide) (by decide) with h462 | h462
                · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h465 | h465
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                        · linarith only [h459, h466, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h461, h466, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · linarith only [h359, h461, h462, h463, h465, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                    · linarith only [h359, h462, h464, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h472 | h472
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h473 | h473
                        · linarith only [h0, h459, h473, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                        · linarith only [h0, h459, h461, h473, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                      · linarith only [h0, h361, h459, h462, h471, h472, hc01, hlam, hphi, u1elo1]
                    · linarith only [h359, h461, h471, hlam]
                · linarith only [h461, h462, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h479 | h479
                · linarith only [h461, h479, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h482 | h482
                    · linarith only [h461, h482, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h484 | h484
                      · linarith only [h482, h484, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
                        · linarith only [h459, h479, h482, h486, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
                          · rcases h0bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [hlam, p489_0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h359, hlam, p489_0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h361, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h413, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p489_1, u1elo1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [hlam, p489_0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo1, u3ehi0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, h481, hc45, hlam, hphi, ht01, ht0b, ht5b, p489_1, u1elo1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, h459, h479, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo1, u3ehi2]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h359, hc01, hlam, hphi, p489_1, u1elo2]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h459, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [hlam, p489_0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h461, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h479, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h361, hc01, hlam, hphi, p489_1, u1elo3]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h460, hlam, p489_0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, h460, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo1, u3ehi0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [hlam, p489_0]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, h459, h460, h479, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo1, u3ehi2]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h413, hc01, hlam, hphi, p489_1, u1elo4]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h460, h481, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h0, h459, h460, h481, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p489_1, u1elo1, u3ehi2]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [h481, hlam, p489_1]
                            · have p489_0 := h489c.1
                              have p489_1 := h489c.2.1
                              have p489_2 := h489c.2.2.1
                              have p489_3 := h489c.2.2.2
                              linarith only [hlam, p489_0]
                          · linarith only [h459, h461, h488, hc45, hlam, hphi, ht34, u3ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                    · linarith only [h459, h461, h516, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h518 | h518
                      · linarith only [h516, h518, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h520 | h520
                        · linarith only [h459, h516, h520, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                          · linarith only [h460, h481, h520, h522, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h461, h522, hc45, hlam, hphi, ht34, u3ehi0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h525 | h525
              · linarith only [h459, h460, h525, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h527 | h527
                · linarith only [h525, h527, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h529 | h529
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h530 | h530
                    · linarith only [h525, h530, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h532 | h532
                      · linarith only [h530, h532, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h534 | h534
                        · linarith only [h361, h459, h460, h530, h534, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
                        · linarith only [h459, h460, h534, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h459, h460, h529, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h538 | h538
            · rcases m.htr 0 3 4 (by decide) (by decide) with h539 | h539
              · rcases m.htr 0 3 5 (by decide) (by decide) with h540 | h540
                · rcases m.htr 0 4 5 (by decide) (by decide) with h541 | h541
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h543 | h543
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h545 | h545
                          · rcases h0bigk with h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h0, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h359, hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h361, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h413, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h359, h459, hc01, hlam, hphi, p546_1, u1elo2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h459, hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h359, h459, h538, h544, h545, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p546_1, u1elo2, u3ehi4]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h359, h459, h540, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p546_1, u1elo2, u3ehi4]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h359, hc01, hlam, hphi, p546_1, u1elo2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h0, h359, hc01, hlam, hphi, p546_1, u1elo2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h359, h538, h544, h545, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p546_1, u1elo2, u3ehi4]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h359, h540, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p546_1, u1elo2, u3ehi4]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h361, h542, hc01, hlam, hphi, p546_1, u1elo2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h538, hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h539, hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h538, h540, hlam, hphi, ht0b, ht34, ht45, ht5b, p546_1, u0elo1, u3ehi4]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h413, h543, hc01, hlam, hphi, p546_1, u1elo2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h538, h541, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h540, hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h541, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                          · linarith only [h359, h459, h538, h541, h545, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                        · linarith only [h459, h539, h544, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h359, h459, h538, h540, h541, h543, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h359, h540, h542, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h579 | h579
                          · linarith only [h359, h459, h538, h541, h578, h579, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases h0bigk with h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h0, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h361, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h413, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, h459, hc01, hlam, hphi, p581_1, u1elo2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h459, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, h459, h538, h578, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p581_1, u1elo2, u3ehi3]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, h459, h538, h541, h578, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p581_1, u1elo2, u3ehi3]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, hc01, hlam, hphi, p581_1, u1elo2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h0, h359, hc01, hlam, hphi, p581_1, u1elo2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, h538, h578, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p581_1, u1elo2, u3ehi3]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, h538, h541, h578, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p581_1, u1elo2, u3ehi3]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h459, h538, h541, h578, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p581_1, u3ehi3]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h538, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h539, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h541, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h413, hc01, hlam, hphi, p581_1, u1elo4]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, h538, h540, h578, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p581_1, u1elo2, u3ehi3]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h540, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h359, h361, h540, hc01, hlam, hphi, p581_1, u1elo2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                        · linarith only [h0, h361, h459, h539, h578, hc01, hlam, hphi, u1elo3]
                      · linarith only [h359, h539, h577, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h359, h539, h576, hlam]
                · linarith only [h539, h540, hc35, hlam, hphi, u3ehi3]
              · linarith only [h459, h538, h539, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h612 | h612
              · rcases m.htr 0 3 5 (by decide) (by decide) with h613 | h613
                · rcases m.htr 0 4 5 (by decide) (by decide) with h614 | h614
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h615 | h615
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h616 | h616
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h617 | h617
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h618 | h618
                          · rcases h0bigk with h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h0, hlam, p619_1]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h359, hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h361, hlam, p619_1]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h413, hlam, p619_1]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h538, h617, hc01, hc23, hlam, hphi, ht12, p619_1]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h459, hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h538, hlam, p619_1]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h359, h413, h538, h612, hc01, hlam, hphi, p619_1, u1elo2]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h359, hc01, hlam, hphi, p619_1, u1elo2]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h0, h359, hc01, hlam, hphi, p619_1, u1elo2]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h359, h361, hc01, hlam, hphi, p619_1, u1elo2]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h359, h413, hc01, hlam, hphi, p619_1, u1elo2]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h361, hc01, hlam, hphi, p619_1, u1elo3]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h0, h361, hc01, hlam, hphi, p619_1, u1elo3]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h612, hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h359, h612, h613, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p619_1, u1elo2, u3ehi4]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h413, h616, hc01, hlam, hphi, p619_1, u1elo2]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h0, h359, h612, h614, hc01, hlam, hphi, p619_1, u1elo2]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h613, hlam, p619_0]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [h614, hlam, p619_1]
                            · have p619_0 := h619c.1
                              have p619_1 := h619c.2.1
                              have p619_2 := h619c.2.2.1
                              have p619_3 := h619c.2.2.2
                              linarith only [hlam, p619_0]
                          · linarith only [h359, h612, h614, h618, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                        · linarith only [h459, h612, h617, hlam]
                      · linarith only [h359, h612, h616, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h359, h612, h615, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h649 | h649
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h650 | h650
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h652 | h652
                          · linarith only [h612, h614, h652, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases h0bigk with h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h0, hlam, p654_1]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h359, hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h361, hlam, p654_1]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h413, hlam, p654_1]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p654_1, u1elo1]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h459, hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h538, hlam, p654_1]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h538, h613, h614, hc45, hlam, hphi, ht34, p654_1, u3ehi4]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h359, hc01, hlam, hphi, p654_1, u1elo2]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h0, h359, hc01, hlam, hphi, p654_1, u1elo2]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h0, h359, h538, hc01, hlam, hphi, p654_1, u1elo2]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h359, h612, h614, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p654_1, u1elo2, u3ehi3]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h614, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p654_1]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h0, h614, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p654_1]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h612, hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h614, hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h413, h650, hc01, hlam, hphi, p654_1, u1elo2]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h0, h413, h650, hc01, hlam, hphi, p654_1, u1elo2]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h613, hlam, p654_0]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [h361, h413, h650, hc01, hlam, hphi, p654_1, u1elo2]
                            · have p654_0 := h654c.1
                              have p654_1 := h654c.2.1
                              have p654_2 := h654c.2.2.1
                              have p654_3 := h654c.2.2.2
                              linarith only [hlam, p654_0]
                        · linarith only [h459, h612, h613, h651, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                      · linarith only [h359, h613, h650, hlam]
                    · linarith only [h359, h612, h649, hlam]
                · linarith only [h612, h613, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h684 | h684
                · linarith only [h612, h684, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
                    · linarith only [h612, h687, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h689 | h689
                      · linarith only [h684, h689, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h691 | h691
                        · linarith only [h359, h687, h691, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h693 | h693
                          · rcases h0bigk with h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [hlam, p694_0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h0, hlam, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h359, hlam, p694_0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h361, hlam, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h413, hlam, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h459, hc01, hc23, hlam, hphi, ht12, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [hlam, p694_0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h459, hlam, p694_0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h538, hlam, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h459, h684, h691, hc34, hlam, hphi, p694_1, u3ehi0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h359, hc01, hlam, hphi, p694_1, u1elo2]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h359, h689, hc02, hc35, hlam, hphi, ht23, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [hlam, p694_0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h612, hlam, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h684, hlam, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h361, hc01, hlam, hphi, p694_1, u1elo3]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h0, h361, hc01, hlam, hphi, p694_1, u1elo3]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h361, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p694_1, u1elo3, u3ehi0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [hlam, p694_0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h361, h684, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p694_1, u1elo3, u3ehi0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h413, hc01, hlam, hphi, p694_1, u1elo4]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h0, h361, h686, hc01, hlam, hphi, p694_1, u1elo3]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h361, h686, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p694_1, u1elo3, u3ehi0]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [h686, hlam, p694_1]
                            · have p694_0 := h694c.1
                              have p694_1 := h694c.2.1
                              have p694_2 := h694c.2.2.1
                              have p694_3 := h694c.2.2.2
                              linarith only [hlam, p694_0]
                          · linarith only [h361, h686, h691, h693, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h721 | h721
                    · linarith only [h612, h721, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                      · linarith only [h721, h723, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h725 | h725
                        · linarith only [h359, h721, h725, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h727 | h727
                          · linarith only [h612, h686, h727, hc34, hlam, hphi, u3ehi0]
                          · linarith only [h612, h727, hc45, hlam, hphi, ht34, u3ehi0]

end R2N4
