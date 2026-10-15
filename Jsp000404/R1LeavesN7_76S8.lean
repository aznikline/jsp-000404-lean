import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_13_14_H_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
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
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h10, h15, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h15, hlam, hphi, ht34, u3ehi2, u4elo3]
                              · linarith only [h14, h9, hc14, hlam, hphi, u4elo0]
                            · linarith only [h13, hlam, hphi, ht34, u3ehi1, u4elo3]
                          · linarith only [h10, h12, h6, h9, hlam, hphi, ht34, u3ehi2, u4elo0]
                        · linarith only [h10, h11, hlam, hphi, ht34, u3ehi2, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                                · linarith only [h0, h10, h22, h26, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h10, h22, h24, h26, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h24, h25, h9, hlam, hphi, ht34, u3ehi3, u4elo0]
                            · linarith only [h24, hlam, hphi, ht34, u3ehi1, u4elo3]
                          · linarith only [h22, h23, h6, h9, hc24, hlam, hphi, u4elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                                  · linarith only [h22, h32, h36, h5, hlam, hphi, ht34, u3ehi4, u4elo0]
                                  · linarith only [h10, h36, h8, h9, hlam, hphi, ht34, u3ehi1, u4elo0]
                                · linarith only [h10, h33, h35, hlam]
                              · linarith only [h33, h34, hlam, hphi, ht34, u3ehi3, u4elo4]
                            · linarith only [h33, hlam, hphi, ht34, u3ehi1, u4elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                                    · rcases h0bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1, u3ehi0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1, u3ehi0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h32, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h32, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h0, hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1, u3ehi1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h0, h32, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h0, h32, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h1, hlam, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h4, hlam, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h32, h6, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h0, h32, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h2, hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h5, hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h7, hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h32, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h3, hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h6, hlam, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h8, hlam, p47_0]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [h9, hlam, p47_1]
                                      · have p47_0 := h47c.1
                                        have p47_1 := h47c.2.1
                                        have p47_2 := h47c.2.2.1
                                        have p47_3 := h47c.2.2.2
                                        linarith only [hlam, p47_0]
                                    · linarith only [h46, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h10, h42, h45, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h10, h42, h44, hlam]
                              · linarith only [h43, h9, hc14, hlam, hphi, u4elo0]
                            · linarith only [h42, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h7, h9, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · linarith only [h7, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h81 | h81
                · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h4, h6, h82, hlam]
                  · linarith only [h81, h82, hc35, hlam, hphi, u3ehi3]
                · linarith only [h81, hlam, hphi, ht34, u3ehi0, u4elo3]
            · linarith only [h4, h5, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
            · rcases m.htr 0 2 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 0 3 4 (by decide) (by decide) with h89 | h89
                · rcases m.htr 0 3 5 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h4, h87, h90, h91, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                                    · rcases h0bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h0, h100, h94, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h0, h100, h4, h94, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, h91, h95, h99, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, h95, h99, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h0, hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h4, hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, h91, h95, h99, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, h4, h95, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h1, hlam, p101_1]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h4, hc02, hc23, hlam, hphi, p101_1]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, h4, h91, h95, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, h4, h95, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h2, hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h87, hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h89, hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, h95, h99, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi4]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h3, hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h88, hlam, p101_1]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h90, hlam, p101_0]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [h91, hlam, p101_1]
                                      · have p101_0 := h101c.1
                                        have p101_1 := h101c.2.1
                                        have p101_2 := h101c.2.2.1
                                        have p101_3 := h101c.2.2.2
                                        linarith only [hlam, p101_0]
                                    · linarith only [h100, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h1, h4, h92, h94, h98, h99, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h4, h98, hc02, hlam, hphi, ht23, ht34, u4elo3]
                              · linarith only [h91, h97, hc14, hlam, hphi, u4elo0]
                            · linarith only [h96, hlam, hphi, ht34, u3ehi1, u4elo3]
                          · linarith only [h4, h88, h94, h95, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h4, h87, h94, hc12, hc23, hlam, hphi]
                    · linarith only [h89, h91, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h89, h90, hc35, hlam, hphi, u3ehi3]
                · linarith only [h89, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h137 | h137
                · rcases m.htr 0 3 5 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h139, h87, h88, hlam]
                    · linarith only [h137, h139, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h137, h138, hc35, hlam, hphi, u3ehi3]
                · linarith only [h137, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h144 | h144
              · rcases m.htr 0 3 4 (by decide) (by decide) with h145 | h145
                · rcases m.htr 0 3 5 (by decide) (by decide) with h146 | h146
                  · linarith only [h144, h146, h87, hlam, hphi, ht34, u3ehi4, u4elo2]
                  · linarith only [h145, h146, hc35, hlam, hphi, u3ehi3]
                · linarith only [h145, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
                · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                      · linarith only [h0, h153, h87, hlam, hphi, ht34, u3ehi2, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h155 | h155
                        · linarith only [h0, h155, h87, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                          · linarith only [h0, h144, h157, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h163 | h163
                                    · rcases h0bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        rcases p164_3 (m.d 0 1) (by simp) with h166 | h166
                                        · rcases p164_3 (m.d 0 2) (by simp) with h167 | h167
                                          · linarith only [h0, h167, hlam]
                                          · rcases p164_3 (m.d 0 3) (by simp) with h169 | h169
                                            · linarith only [h1, h169, hlam]
                                            · linarith only [h169, h4, hlam]
                                        · linarith only [h0, h166, hlam]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h1, h159, h163, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p164_1, u3ehi4]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h159, h163, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p164_1, u3ehi4]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h151, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p164_1, u3ehi4]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h0, hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h4, hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h87, hlam, p164_1]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h144, hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h1, hlam, p164_1]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h4, hc02, hc23, hlam, hphi, p164_1]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h159, h163, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p164_1, u3ehi4]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h151, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p164_1, u3ehi4]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h2, hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p164_1, u4elo0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h150, hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h151, h87, hlam, hphi, ht34, p164_1, u3ehi4, u4elo2]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h3, hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h0, h144, hc12, hc25, hlam, hphi, p164_1]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h151, hlam, p164_0]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [h152, hlam, p164_1]
                                      · have p164_0 := h164c.1
                                        have p164_1 := h164c.2.1
                                        have p164_2 := h164c.2.2.1
                                        have p164_3 := h164c.2.2.2
                                        linarith only [hlam, p164_0]
                                    · linarith only [h163, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h150, h162, h4, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h159, h161, h2, h4, h87, hlam, hphi, ht34, u3ehi0, u4elo2]
                              · linarith only [h152, h160, h87, hc14, hlam, hphi, u4elo2]
                            · linarith only [h159, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h150, h152, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h150, h151, hc35, hlam, hphi, u3ehi3]
                · linarith only [h150, hlam, hphi, ht34, u3ehi0, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h204 | h204
          · rcases m.htr 0 2 4 (by decide) (by decide) with h205 | h205
            · rcases m.htr 0 2 5 (by decide) (by decide) with h206 | h206
              · linarith only [h0, h206, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
                · rcases m.htr 0 3 5 (by decide) (by decide) with h209 | h209
                  · linarith only [h0, h204, h209, h3, hlam]
                  · linarith only [h208, h209, hc35, hlam, hphi, u3ehi3]
                · linarith only [h208, hlam, hphi, ht34, u3ehi0, u4elo3]
            · linarith only [h204, h205, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h214 | h214
            · rcases m.htr 0 2 5 (by decide) (by decide) with h215 | h215
              · linarith only [h0, h215, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
                · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
                  · linarith only [h1, h218, h3, hlam]
                  · linarith only [h217, h218, hc35, hlam, hphi, u3ehi3]
                · linarith only [h217, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h222 | h222
              · linarith only [h1, h214, h222, h3, hlam, hphi, ht34, u3ehi1, u4elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h224 | h224
                · rcases m.htr 0 3 5 (by decide) (by decide) with h225 | h225
                  · linarith only [h1, h225, h3, hlam]
                  · linarith only [h224, h225, hc35, hlam, hphi, u3ehi3]
                · linarith only [h224, hlam, hphi, ht34, u3ehi0, u4elo3]
      · linarith only [h1, h2, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h230 | h230
      · rcases m.htr 0 1 5 (by decide) (by decide) with h231 | h231
        · rcases m.htr 0 2 3 (by decide) (by decide) with h232 | h232
          · linarith only [h0, h1, h232, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h234 | h234
            · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
              · rcases m.htr 0 3 4 (by decide) (by decide) with h236 | h236
                · rcases m.htr 0 3 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                      · linarith only [h0, h1, h232, h239, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                                · linarith only [h0, h1, h239, h241, h245, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h1, h239, h245, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h243, h244, hlam, hphi, ht34, u3ehi3, u4elo4]
                            · linarith only [h0, h1, h241, h243, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h235, h241, h242, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1, h234, h239, h241, hc12, hc23, hlam, hphi]
                    · linarith only [h236, h238, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h236, h237, hc35, hlam, hphi, u3ehi3]
                · linarith only [h236, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h255 | h255
                · rcases m.htr 0 3 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
                    · linarith only [h234, h235, h257, hlam]
                    · linarith only [h255, h257, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h255, h256, hc35, hlam, hphi, u3ehi3]
                · linarith only [h255, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
              · rcases m.htr 0 3 4 (by decide) (by decide) with h263 | h263
                · rcases m.htr 0 3 5 (by decide) (by decide) with h264 | h264
                  · linarith only [h234, h262, h264, hlam, hphi, ht34, u3ehi4, u4elo2]
                  · linarith only [h263, h264, hc35, hlam, hphi, u3ehi3]
                · linarith only [h263, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h268 | h268
                · rcases m.htr 0 3 5 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                      · linarith only [h0, h1, h271, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                        · linarith only [h0, h234, h273, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                          · linarith only [h0, h262, h275, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                                    · rcases h0bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h1, h271, hc02, hc23, hlam, hphi, p282_1]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h1, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h1, h230, h271, h277, h281, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p282_1, u3ehi4]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h1, h269, h271, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p282_1, u3ehi4]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h0, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h232, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h234, hlam, p282_1]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h262, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p282_1]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h0, h1, h271, hc12, hc23, hlam, hphi, p282_1]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h1, h230, h271, h277, h281, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p282_1, u3ehi4]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h1, h269, h271, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p282_1, u3ehi4]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h230, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p282_1, u4elo0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h268, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h234, h269, hlam, hphi, ht34, p282_1, u3ehi4, u4elo2]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h231, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h0, h1, h231, h271, hc12, hc23, hlam, hphi, p282_1]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h269, hlam, p282_0]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [h270, hlam, p282_1]
                                      · have p282_0 := h282c.1
                                        have p282_1 := h282c.2.1
                                        have p282_2 := h282c.2.2.1
                                        have p282_3 := h282c.2.2.2
                                        linarith only [hlam, p282_0]
                                    · linarith only [h281, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h1, h230, h271, h278, h280, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h230, h271, h277, h279, hlam]
                              · linarith only [h277, h278, hlam, hphi, ht34, u3ehi3, u4elo4]
                            · linarith only [h1, h277, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h268, h270, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h268, h269, hc35, hlam, hphi, u3ehi3]
                · linarith only [h268, hlam, hphi, ht34, u3ehi0, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h316 | h316
          · linarith only [h0, h1, h316, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
            · rcases m.htr 0 2 5 (by decide) (by decide) with h319 | h319
              · linarith only [h0, h231, h319, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 3 5 (by decide) (by decide) with h322 | h322
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
                    · linarith only [h230, h231, h323, hlam]
                    · linarith only [h321, h323, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h321, h322, hc35, hlam, hphi, u3ehi3]
                · linarith only [h321, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
              · linarith only [h0, h231, h318, h328, hc12, hlam, hphi, ht23, ht34, u4elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h330 | h330
                · rcases m.htr 0 3 5 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                    · linarith only [h230, h231, h332, hlam]
                    · linarith only [h330, h332, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h330, h331, hc35, hlam, hphi, u3ehi3]
                · linarith only [h330, hlam, hphi, ht34, u3ehi0, u4elo3]
      · linarith only [h0, h230, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h338 | h338
    · rcases m.htr 0 1 4 (by decide) (by decide) with h339 | h339
      · rcases m.htr 0 1 5 (by decide) (by decide) with h340 | h340
        · rcases m.htr 0 2 3 (by decide) (by decide) with h341 | h341
          · rcases m.htr 0 2 4 (by decide) (by decide) with h342 | h342
            · rcases m.htr 0 2 5 (by decide) (by decide) with h343 | h343
              · rcases m.htr 0 3 4 (by decide) (by decide) with h344 | h344
                · rcases m.htr 0 3 5 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h350 | h350
                            · linarith only [h0, h338, h350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h350, hlam, hphi, ht34, u3ehi1, u4elo3]
                          · linarith only [h0, h338, h347, h349, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h338, h347, h348, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h338, h347, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h344, h346, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h344, h345, hc35, hlam, hphi, u3ehi3]
                · linarith only [h344, hlam, hphi, ht34, u3ehi0, u4elo3]
              · linarith only [h0, h340, h343, hlam]
            · linarith only [h0, h338, h342, hlam, hphi, ht34, u3ehi1, u4elo2]
          · linarith only [h0, h338, h341, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h362 | h362
          · rcases m.htr 0 2 4 (by decide) (by decide) with h363 | h363
            · rcases m.htr 0 2 5 (by decide) (by decide) with h364 | h364
              · rcases m.htr 0 3 4 (by decide) (by decide) with h365 | h365
                · rcases m.htr 0 3 5 (by decide) (by decide) with h366 | h366
                  · linarith only [h338, h340, h366, hlam]
                  · linarith only [h365, h366, hc35, hlam, hphi, u3ehi3]
                · linarith only [h365, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h370 | h370
                · rcases m.htr 0 3 5 (by decide) (by decide) with h371 | h371
                  · linarith only [h0, h338, h364, h371, hlam]
                  · linarith only [h370, h371, hc35, hlam, hphi, u3ehi3]
                · linarith only [h370, hlam, hphi, ht34, u3ehi0, u4elo3]
            · linarith only [h0, h338, h363, hlam, hphi, ht34, u3ehi1, u4elo2]
          · linarith only [h0, h338, h362, hlam]
      · linarith only [h338, h339, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h378 | h378
      · rcases m.htr 0 1 5 (by decide) (by decide) with h379 | h379
        · rcases m.htr 0 2 3 (by decide) (by decide) with h380 | h380
          · rcases m.htr 0 2 4 (by decide) (by decide) with h381 | h381
            · rcases m.htr 0 2 5 (by decide) (by decide) with h382 | h382
              · rcases m.htr 0 3 4 (by decide) (by decide) with h383 | h383
                · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h388 | h388
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h389 | h389
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h390 | h390
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h393 | h393
                                    · rcases h0bigk with h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h338, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h338, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h338, h379, h388, h392, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p394_1, u3ehi4]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, h338, h378, h387, h391, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p394_1, u3ehi3]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, h378, h387, h391, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p394_1, u3ehi3]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, h379, h388, h392, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p394_1, u3ehi4]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h378, h387, h391, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1, u3ehi3]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h380, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, h378, h380, h387, h391, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p394_1, u3ehi3]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h0, h379, h380, h388, h392, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p394_1, u3ehi4]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h378, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h381, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h383, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h379, h388, h392, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p394_1, u3ehi4]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h379, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h382, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h384, hlam, p394_0]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [h385, hlam, p394_1]
                                      · have p394_0 := h394c.1
                                        have p394_1 := h394c.2.1
                                        have p394_2 := h394c.2.2.1
                                        have p394_3 := h394c.2.2.2
                                        linarith only [hlam, p394_0]
                                    · linarith only [h393, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h391, h392, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h391, hlam, hphi, ht34, u3ehi2, u4elo3]
                              · linarith only [h389, h390, hlam, hphi, ht34, u3ehi3, u4elo4]
                            · linarith only [h338, h389, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h382, h388, hlam]
                        · linarith only [h338, h378, h384, h385, h386, h387, hlam, hphi, ht34, u3ehi4, u4elo2]
                      · linarith only [h0, h380, h386, hlam]
                    · linarith only [h383, h385, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h383, h384, hc35, hlam, hphi, u3ehi3]
                · linarith only [h383, hlam, hphi, ht34, u3ehi0, u4elo3]
              · linarith only [h0, h379, h382, hlam]
            · linarith only [h380, h381, hlam, hphi, ht34, u3ehi0, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h433 | h433
            · rcases m.htr 0 2 5 (by decide) (by decide) with h434 | h434
              · rcases m.htr 0 3 4 (by decide) (by decide) with h435 | h435
                · rcases m.htr 0 3 5 (by decide) (by decide) with h436 | h436
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h437 | h437
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                            · linarith only [h0, h378, h380, h438, h441, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h378, h380, h435, h438, h441, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h378, h380, h436, h437, h438, h440, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h378, h380, h436, h437, h438, h439, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                            · linarith only [h0, h378, h438, h448, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h338, h448, hlam, hphi, ht34, u3ehi0, u4elo3]
                          · linarith only [h0, h378, h434, h436, h437, h447, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h378, h436, h437, h446, hlam, hphi, ht34, u3ehi4, u4elo2]
                    · linarith only [h435, h437, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h435, h436, hc35, hlam, hphi, u3ehi3]
                · linarith only [h435, hlam, hphi, ht34, u3ehi0, u4elo3]
              · linarith only [h0, h379, h434, hlam]
            · linarith only [h0, h378, h433, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h458 | h458
          · rcases m.htr 0 2 4 (by decide) (by decide) with h459 | h459
            · rcases m.htr 0 2 5 (by decide) (by decide) with h460 | h460
              · rcases m.htr 0 3 4 (by decide) (by decide) with h461 | h461
                · rcases m.htr 0 3 5 (by decide) (by decide) with h462 | h462
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
                    · linarith only [h378, h379, h463, hlam]
                    · linarith only [h461, h463, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h461, h462, hc35, hlam, hphi, u3ehi3]
                · linarith only [h461, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h468 | h468
                · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
                  · linarith only [h458, h460, h469, hlam]
                  · linarith only [h468, h469, hc35, hlam, hphi, u3ehi3]
                · linarith only [h468, hlam, hphi, ht34, u3ehi0, u4elo3]
            · linarith only [h0, h378, h459, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h474 | h474
            · rcases m.htr 0 2 5 (by decide) (by decide) with h475 | h475
              · rcases m.htr 0 3 4 (by decide) (by decide) with h476 | h476
                · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
                    · linarith only [h378, h379, h478, hlam]
                    · linarith only [h476, h478, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h476, h477, hc35, hlam, hphi, u3ehi3]
                · linarith only [h476, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h483 | h483
                · rcases m.htr 0 3 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h485 | h485
                    · linarith only [h0, h378, h475, h485, hlam]
                    · linarith only [h483, h485, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h483, h484, hc35, hlam, hphi, u3ehi3]
                · linarith only [h483, hlam, hphi, ht34, u3ehi0, u4elo3]
            · linarith only [h0, h378, h474, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h491 | h491
        · rcases m.htr 0 2 3 (by decide) (by decide) with h492 | h492
          · rcases m.htr 0 2 4 (by decide) (by decide) with h493 | h493
            · rcases m.htr 0 2 5 (by decide) (by decide) with h494 | h494
              · rcases m.htr 0 3 4 (by decide) (by decide) with h495 | h495
                · rcases m.htr 0 3 5 (by decide) (by decide) with h496 | h496
                  · linarith only [h378, h491, h496, hlam, hphi, ht34, u3ehi4, u4elo1]
                  · linarith only [h495, h496, hc35, hlam, hphi, u3ehi3]
                · linarith only [h495, hlam, hphi, ht34, u3ehi0, u4elo3]
              · linarith only [h378, h491, h492, h494, hlam, hphi, ht34, u3ehi2, u4elo1]
            · linarith only [h492, h493, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h502 | h502
            · rcases m.htr 0 2 5 (by decide) (by decide) with h503 | h503
              · rcases m.htr 0 3 4 (by decide) (by decide) with h504 | h504
                · rcases m.htr 0 3 5 (by decide) (by decide) with h505 | h505
                  · linarith only [h378, h491, h505, hlam, hphi, ht34, u3ehi4, u4elo1]
                  · linarith only [h504, h505, hc35, hlam, hphi, u3ehi3]
                · linarith only [h504, hlam, hphi, ht34, u3ehi0, u4elo3]
              · linarith only [h378, h491, h502, h503, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h510 | h510
              · rcases m.htr 0 3 4 (by decide) (by decide) with h511 | h511
                · rcases m.htr 0 3 5 (by decide) (by decide) with h512 | h512
                  · linarith only [h0, h491, h502, h512, hlam, hphi, ht34, u3ehi4, u4elo2]
                  · linarith only [h511, h512, hc35, hlam, hphi, u3ehi3]
                · linarith only [h511, hlam, hphi, ht34, u3ehi0, u4elo3]
              · linarith only [h0, h491, h510, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h517 | h517
          · rcases m.htr 0 2 4 (by decide) (by decide) with h518 | h518
            · rcases m.htr 0 2 5 (by decide) (by decide) with h519 | h519
              · rcases m.htr 0 3 4 (by decide) (by decide) with h520 | h520
                · rcases m.htr 0 3 5 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h525 | h525
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h528 | h528
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h529 | h529
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h530 | h530
                                    · rcases h0bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, hlam, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h338, hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h378, hlam, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h491, hlam, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, h517, h528, h530, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p531_1, u3ehi4]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, h378, hc01, hc12, hlam, hphi, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, h519, h529, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p531_1, u3ehi4]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h338, hc01, hc13, hlam, hphi, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h517, hlam, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, h378, h517, hc01, hc12, hlam, hphi, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, h517, h519, h529, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p531_1, u3ehi4]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p531_1, u4elo0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h518, hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h520, hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h378, h519, h529, hlam, hphi, ht34, p531_1, u3ehi4, u4elo1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h0, h491, h517, h527, h528, h530, hc01, hc12, hlam, hphi, ht34, p531_1, u3ehi4, u4elo1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h519, hlam, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h521, hlam, p531_0]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [h522, hlam, p531_1]
                                      · have p531_0 := h531c.1
                                        have p531_1 := h531c.2.1
                                        have p531_2 := h531c.2.2.1
                                        have p531_3 := h531c.2.2.2
                                        linarith only [hlam, p531_0]
                                    · linarith only [h530, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h528, h529, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h528, hlam, hphi, ht34, u3ehi2, u4elo3]
                              · linarith only [h378, h522, h527, hlam]
                            · linarith only [h526, hlam, hphi, ht34, u3ehi1, u4elo3]
                          · linarith only [h0, h519, h525, hlam]
                        · linarith only [h0, h518, h524, hlam]
                      · linarith only [h0, h517, h523, hlam]
                    · linarith only [h520, h522, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h520, h521, hc35, hlam, hphi, u3ehi3]
                · linarith only [h520, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h568 | h568
                · rcases m.htr 0 3 5 (by decide) (by decide) with h569 | h569
                  · linarith only [h517, h519, h569, hlam]
                  · linarith only [h568, h569, hc35, hlam, hphi, u3ehi3]
                · linarith only [h568, hlam, hphi, ht34, u3ehi0, u4elo3]
            · linarith only [h517, h518, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h574 | h574
            · rcases m.htr 0 2 5 (by decide) (by decide) with h575 | h575
              · rcases m.htr 0 3 4 (by decide) (by decide) with h576 | h576
                · rcases m.htr 0 3 5 (by decide) (by decide) with h577 | h577
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h583 | h583
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                                · linarith only [h517, h574, h579, h584, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h517, h574, h576, h584, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h578, h583, hc14, hlam, hphi, u4elo0]
                            · linarith only [h517, h574, h576, h579, h582, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h517, h575, h579, h581, hlam]
                        · linarith only [h517, h579, h580, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h591 | h591
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h592 | h592
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h593 | h593
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h594 | h594
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h596 | h596
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h597 | h597
                                    · rcases h0bigk with h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h0, hlam, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h338, hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h378, hlam, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h491, hlam, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h517, hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h0, h575, h578, h579, h596, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p598_1, u3ehi4]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h0, h575, h579, h596, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p598_1, u3ehi4]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h338, hc01, hc13, hlam, hphi, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h517, hc02, hc23, hlam, hphi, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h517, h575, h578, h596, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p598_1, u3ehi4]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h517, h575, h596, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p598_1, u3ehi4]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p598_1, u4elo0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h574, hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h576, hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h378, h575, h596, hlam, hphi, ht34, p598_1, u3ehi4, u4elo1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h491, hc01, hc15, hlam, hphi, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h575, hlam, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h577, hlam, p598_0]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [h578, hlam, p598_1]
                                      · have p598_0 := h598c.1
                                        have p598_1 := h598c.2.1
                                        have p598_2 := h598c.2.2.1
                                        have p598_3 := h598c.2.2.2
                                        linarith only [hlam, p598_0]
                                    · linarith only [h597, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h0, h579, h596, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h574, h577, h578, h579, h595, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h0, h378, h574, h578, h594, hc01, hc12, hlam, hphi]
                            · linarith only [h338, h378, h576, h593, hlam, hphi, ht34, u3ehi0, u4elo1]
                          · linarith only [h0, h575, h592, hlam]
                        · linarith only [h0, h574, h591, hlam]
                    · linarith only [h576, h578, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h576, h577, hc35, hlam, hphi, u3ehi3]
                · linarith only [h576, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h634 | h634
                · rcases m.htr 0 3 5 (by decide) (by decide) with h635 | h635
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h636 | h636
                    · linarith only [h574, h575, h636, hlam]
                    · linarith only [h634, h636, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h634, h635, hc35, hlam, hphi, u3ehi3]
                · linarith only [h634, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h641 | h641
              · rcases m.htr 0 3 4 (by decide) (by decide) with h642 | h642
                · rcases m.htr 0 3 5 (by decide) (by decide) with h643 | h643
                  · linarith only [h574, h641, h643, hlam, hphi, ht34, u3ehi4, u4elo2]
                  · linarith only [h642, h643, hc35, hlam, hphi, u3ehi3]
                · linarith only [h642, hlam, hphi, ht34, u3ehi0, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h647 | h647
                · rcases m.htr 0 3 5 (by decide) (by decide) with h648 | h648
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h654 | h654
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h655 | h655
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h656 | h656
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h657 | h657
                                    · rcases h0bigk with h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h0, hlam, p658_1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h338, hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h378, hlam, p658_1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h491, hlam, p658_1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h641, h652, h654, hc01, hlam, hphi, ht12, ht23, ht34, p658_1, u4elo1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h517, hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h574, hlam, p658_1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h641, hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h517, h650, hc01, hc12, hlam, hphi, p658_1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h517, h650, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p658_1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h0, h517, h641, h648, h649, h650, h652, h654, hc01, hc12, hlam, hphi, ht34, p658_1, u3ehi4, u4elo1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h0, h517, h641, h648, h650, h652, h654, hc01, hc12, hlam, hphi, ht34, p658_1, u3ehi4, u4elo1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p658_1, u4elo0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h0, h574, h651, hc01, hlam, hphi, ht12, ht23, ht34, p658_1, u4elo1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h647, hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h574, h648, h651, hlam, hphi, ht34, p658_1, u3ehi4, u4elo1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h491, h517, h647, h650, h654, h657, hc01, hc12, hlam, hphi, ht34, p658_1, u3ehi4, u4elo1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h0, h517, h641, h647, h650, h652, h654, h657, hc01, hc12, hlam, hphi, ht34, p658_1, u3ehi4, u4elo1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h648, hlam, p658_0]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [h649, hlam, p658_1]
                                      · have p658_0 := h658c.1
                                        have p658_1 := h658c.2.1
                                        have p658_2 := h658c.2.2.1
                                        have p658_3 := h658c.2.2.2
                                        linarith only [hlam, p658_0]
                                    · linarith only [h657, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h517, h647, h656, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h517, h647, h655, hlam]
                              · linarith only [h574, h649, h651, h654, hlam]
                            · linarith only [h517, h647, h650, h653, hlam]
                          · linarith only [h517, h647, h650, h652, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h517, h647, h650, h651, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
                        · linarith only [h0, h574, h650, h691, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h691, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h647, h649, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h647, h648, hc35, hlam, hphi, u3ehi3]
                · linarith only [h647, hlam, hphi, ht34, u3ehi0, u4elo3]

end R2N4
