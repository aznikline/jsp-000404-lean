import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_14_L_R_L_I_L_0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h10, h12, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h12, h2, h9, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h10, h11, h5, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h10, h16, h5, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                          · rcases h3bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, h16, h18, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              rcases p19_3 (m.d 0 3) (by simp) with h22 | h22
                              · rcases p19_3 (m.d 1 3) (by simp) with h23 | h23
                                · linarith only [h1, h23, hlam]
                                · linarith only [h23, h5, hlam]
                              · linarith only [h22, h3, hlam]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              rcases p19_3 (m.d 0 3) (by simp) with h27 | h27
                              · rcases p19_3 (m.d 1 3) (by simp) with h28 | h28
                                · linarith only [h1, h28, hlam]
                                · linarith only [h28, h7, hlam]
                              · linarith only [h27, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              rcases p19_3 (m.d 0 3) (by simp) with h32 | h32
                              · rcases p19_3 (m.d 1 3) (by simp) with h33 | h33
                                · linarith only [h1, h33, hlam]
                                · linarith only [h33, h8, hlam]
                              · linarith only [h32, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h1, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              rcases p19_3 (m.d 0 3) (by simp) with h39 | h39
                              · rcases p19_3 (m.d 1 3) (by simp) with h40 | h40
                                · rcases p19_3 (m.d 2 3) (by simp) with h41 | h41
                                  · linarith only [h41, h5, hlam]
                                  · rcases p19_3 (m.d 3 4) (by simp) with h43 | h43
                                    · linarith only [h43, h7, hlam]
                                    · linarith only [h10, h43, hlam]
                                · linarith only [h40, h5, hlam]
                              · linarith only [h3, h39, hlam]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h1, h16, h18, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, h16, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h3, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h5, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h10, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h16, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hc03, hlam, hphi, ht34, p19_1, u4elo3]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h7, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, h16, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h4, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h8, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h18, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                          · linarith only [h18, h2, h9, hc34, hlam, hphi, u4elo0]
                    · linarith only [h9, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                    · linarith only [h67, h7, h8, hlam]
                    · linarith only [h67, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
              · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                          · linarith only [h0, h3, h5, h72, h76, h78, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h3, h5, h72, h75, h78, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h5, h72, h74, h75, h77, hc13, hlam, hphi, u1ehi4]
                      · linarith only [h5, h72, h75, h76, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                    · linarith only [h75, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                    · linarith only [h5, h72, h74, h84, hlam]
                    · linarith only [h84, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                · linarith only [h5, h72, h73, hc24, hlam, hphi, u4elo3]
              · linarith only [h72, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
            · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h1, h4, h92, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                    · linarith only [h91, h92, h94, hlam]
                    · linarith only [h94, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                · linarith only [h91, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
              · linarith only [h90, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
            · linarith only [h3, h4, h89, hc35, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h100 | h100
          · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
            · linarith only [h0, h101, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
              · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                          · rcases h3bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h101, h103, h107, h109, hc03, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h3, hlam, p110_1]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              rcases p110_3 (m.d 0 3) (by simp) with h114 | h114
                              · rcases p110_3 (m.d 1 3) (by simp) with h115 | h115
                                · linarith only [h1, h115, hlam]
                                · linarith only [h104, h115, hlam]
                              · linarith only [h114, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              rcases p110_3 (m.d 0 3) (by simp) with h119 | h119
                              · rcases p110_3 (m.d 1 3) (by simp) with h120 | h120
                                · linarith only [h1, h120, hlam]
                                · linarith only [h105, h120, hlam]
                              · linarith only [h119, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h1, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h101, hlam, p110_1]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h1, h109, hc01, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              rcases p110_3 (m.d 0 3) (by simp) with h128 | h128
                              · rcases p110_3 (m.d 1 3) (by simp) with h129 | h129
                                · rcases p110_3 (m.d 2 3) (by simp) with h130 | h130
                                  · rcases p110_3 (m.d 3 4) (by simp) with h131 | h131
                                    · linarith only [h104, h131, hlam]
                                    · linarith only [h109, h131, hlam]
                                  · linarith only [h108, h130, hlam]
                                · linarith only [h129, hlam, p110_0]
                              · linarith only [h100, h128, hlam]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h1, hc23, hlam, hphi, ht12, p110_1, u1ehi2]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [hc23, hlam, hphi, ht12, p110_1, u1ehi2]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              rcases p110_3 (m.d 0 3) (by simp) with h140 | h140
                              · linarith only [h140, h3, hlam]
                              · linarith only [h0, h103, h107, h140, h3, hlam]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              rcases p110_3 (m.d 0 3) (by simp) with h143 | h143
                              · linarith only [h143, h3, hlam]
                              · linarith only [h100, h143, hlam]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h0, h103, h107, h3, hlam, p110_1]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h104, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h107, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h0, h103, h107, h3, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p110_1]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h100, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h105, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h108, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [h109, hlam, p110_0]
                            · have p110_0 := h110c.1
                              have p110_1 := h110c.2.1
                              have p110_2 := h110c.2.2.1
                              have p110_3 := h110c.2.2.2
                              linarith only [hlam, p110_0]
                          · linarith only [h106, h109, h2, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h108, h3, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h0, h107, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h106, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                  · linarith only [h100, h101, h103, h105, h3, hc23, hlam, hphi, ht12, u1ehi3]
                · linarith only [h101, h103, h104, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo3]
              · linarith only [h103, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
            · linarith only [h0, h163, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                · rcases m.htr 1 3 5 (by decide) (by decide) with h167 | h167
                  · linarith only [h1, h100, h167, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
                    · linarith only [h163, h165, h167, h169, hlam]
                    · linarith only [h169, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                · linarith only [h163, h165, h166, hc24, hlam, hphi, u4elo3]
              · linarith only [h165, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h176 | h176
    · linarith only [h0, h176, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h178 | h178
      · linarith only [h0, h178, hc12, hlam, hphi, u1ehi3]
      · linarith only [h178, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_11_13_25_L_I_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h1, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h12, h4, h6, h9, hlam]
                      · linarith only [h12, h4, h6, hc23, hlam, hphi, u3elo4]
                    · linarith only [h11, h8, h9, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h5, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h18, h8, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h16, h20, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
                      · linarith only [h18, h20, h5, h6, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
              · linarith only [h23, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                · linarith only [h25, h4, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                  · linarith only [h25, h27, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h25, h29, hc13, hlam, hphi, u3elo2]
                    · linarith only [h29, h4, h5, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
            · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
              · linarith only [h33, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h36, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h36, h39, h4, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h32, h38, h39, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h32, h38, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h32, h35, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
              · linarith only [h4, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                  · linarith only [h47, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h32, h46, h47, h50, hc12, hlam, hphi, ht23, u3elo2]
                      · linarith only [h4, h50, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h4, h49, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                  · linarith only [h46, h54, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                    · linarith only [h46, h56, hc13, hlam, hphi, u3elo2]
                    · linarith only [h4, h56, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
          · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
            · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
              · linarith only [h0, h3, h61, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                  · linarith only [h0, h3, h59, h61, h64, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3, h59, h64, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h67 | h67
                  · linarith only [h0, h3, h60, h61, h63, h67, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3, h59, h67, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
              · linarith only [h2, h60, h70, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                · linarith only [h59, h60, h72, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                  · linarith only [h2, h3, h59, h60, h70, h74, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h2, h3, h60, h74, hc12, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
            · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
              · linarith only [h1, h59, h78, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                  · linarith only [h1, h3, h78, h81, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h1, h3, h59, h81, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h59, h77, h80, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
              · linarith only [h1, h59, h85, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                  · linarith only [h1, h3, h85, h88, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h1, h3, h77, h87, h88, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h87, h91, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h2, h3, h87, h91, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h94 | h94
        · linarith only [h2, h94, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
          · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
            · linarith only [h0, h2, h97, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
              · linarith only [h0, h2, h97, h99, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                · linarith only [h0, h101, h2, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h101, h2, h96, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
            · linarith only [h1, h104, h2, h96, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
              · linarith only [h106, h96, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                · linarith only [h1, h108, h2, hlam]
                · linarith only [h1, h108, h2, h96, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h112 | h112
    · rcases m.htr 0 1 4 (by decide) (by decide) with h113 | h113
      · rcases m.htr 0 1 5 (by decide) (by decide) with h114 | h114
        · linarith only [h0, h114, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
          · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
            · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
              · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                  · linarith only [h112, h120, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
                  · linarith only [h112, h114, h120, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h123 | h123
                  · linarith only [h113, h119, h123, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h112, h114, h123, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                · linarith only [h0, h112, h118, h126, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h113, h118, h126, h128, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h113, h118, h126, h128, hc13, hlam, hphi, u3elo4]
            · linarith only [h0, h113, h117, hlam]
          · linarith only [h0, h116, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h133 | h133
        · linarith only [h0, h133, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
          · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
            · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
              · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                · linarith only [h112, h113, h138, hlam]
                · linarith only [h112, h113, h135, h138, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                · linarith only [h0, h112, h137, h141, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h112, h113, h141, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
              · linarith only [h136, h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                · linarith only [h0, h112, h136, h146, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h112, h136, h146, hc13, hlam, hphi, u3elo3]
          · linarith only [h0, h112, h135, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h150 | h150
      · rcases m.htr 0 1 5 (by decide) (by decide) with h151 | h151
        · linarith only [h112, h151, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
          · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
            · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
              · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                  · linarith only [h157, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                  · linarith only [h112, h157, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h112, h150, h154, h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h162, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                  · linarith only [h112, h150, h154, h162, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h112, h150, h154, h161, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h112, h150, h153, h154, hc23, hlam, hphi, u3elo0]
          · linarith only [h0, h153, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h168 | h168
        · linarith only [h0, h168, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
          · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
            · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
              · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h174, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                  · linarith only [h150, h173, h174, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h112, h173, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
                · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
                  · linarith only [h179, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                  · linarith only [h112, h179, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h112, h178, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
              · linarith only [h171, h183, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                · linarith only [h170, h171, h185, hlam]
                · linarith only [h112, h185, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h170, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_11_13_25_L_R_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h10, h9, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h5, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h15, h5, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · linarith only [h15, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h8, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                    · linarith only [h20, h22, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h24, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h20, h24, h6, hc23, hc34, hlam, hphi]
                  · linarith only [h20, h21, h6, hlam, hphi, u5ehi8, u5elo4]
                · linarith only [h20, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h1, h29, h34, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · rcases h3bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h0, h29, h3, h31, h34, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p36_1, u1ehi1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 3) (by simp) with h40 | h40
                            · rcases p36_3 (m.d 1 3) (by simp) with h41 | h41
                              · linarith only [h1, h41, hlam]
                              · linarith only [h29, h41, hlam]
                            · linarith only [h40, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 3) (by simp) with h45 | h45
                            · rcases p36_3 (m.d 1 3) (by simp) with h46 | h46
                              · linarith only [h1, h46, hlam]
                              · linarith only [h30, h46, hlam]
                            · linarith only [h45, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h1, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h5, hlam, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 3) (by simp) with h53 | h53
                            · rcases p36_3 (m.d 1 3) (by simp) with h54 | h54
                              · rcases p36_3 (m.d 2 3) (by simp) with h55 | h55
                                · rcases p36_3 (m.d 3 4) (by simp) with h56 | h56
                                  · linarith only [h56, hlam, p36_0]
                                  · rcases p36_3 (m.d 3 5) (by simp) with h58 | h58
                                    · linarith only [h30, h58, hlam]
                                    · linarith only [h34, h58, hlam]
                                · linarith only [h32, h55, hlam]
                              · linarith only [h54, hlam, p36_0]
                            · linarith only [h1, h29, h31, h34, h53, hlam]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi8]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h3, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h29, h31, h34, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            rcases p36_3 (m.d 0 3) (by simp) with h68 | h68
                            · rcases p36_3 (m.d 1 3) (by simp) with h69 | h69
                              · linarith only [h5, h69, hlam]
                              · linarith only [h29, h69, hlam]
                            · linarith only [h29, h3, h31, h34, h5, h68, hc13, hlam, hphi, u1ehi1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p36_1, u5ehi8]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h29, h3, h31, h34, h5, hlam, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h29, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h32, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h34, hlam, p36_1]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h4, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h30, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h33, hlam, p36_0]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [h33, hc34, hlam, hphi, ht45, p36_1, u5elo2]
                          · have p36_0 := h36c.1
                            have p36_1 := h36c.2.1
                            have p36_2 := h36c.2.2.1
                            have p36_3 := h36c.2.2.2
                            linarith only [hlam, p36_0]
                      · linarith only [h30, h33, h5, hlam]
                    · linarith only [h32, h5, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h31, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h30, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                    · linarith only [h0, h29, h3, h88, h90, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · linarith only [h5, h90, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h29, h88, h89, hlam, hphi, u5ehi8, u5elo4]
                · linarith only [h88, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
          · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
            · linarith only [h0, h3, h97, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
              · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                        · linarith only [h1, h104, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · rcases h3bigk with h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h3, hc23, hlam, hphi, ht12, p106_1, u1ehi2]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h3, hlam, p106_1]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            rcases p106_3 (m.d 0 3) (by simp) with h110 | h110
                            · rcases p106_3 (m.d 1 3) (by simp) with h111 | h111
                              · linarith only [h1, h111, hlam]
                              · linarith only [h111, h99, hlam]
                            · linarith only [h110, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            rcases p106_3 (m.d 0 3) (by simp) with h115 | h115
                            · rcases p106_3 (m.d 1 3) (by simp) with h116 | h116
                              · linarith only [h1, h116, hlam]
                              · linarith only [h100, h116, hlam]
                            · linarith only [h115, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h1, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h97, hlam, p106_1]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            rcases p106_3 (m.d 0 3) (by simp) with h123 | h123
                            · rcases p106_3 (m.d 1 3) (by simp) with h124 | h124
                              · rcases p106_3 (m.d 2 3) (by simp) with h125 | h125
                                · rcases p106_3 (m.d 3 4) (by simp) with h126 | h126
                                  · linarith only [h126, hlam, p106_0]
                                  · rcases p106_3 (m.d 3 5) (by simp) with h128 | h128
                                    · linarith only [h100, h128, hlam]
                                    · linarith only [h104, h128, hlam]
                                · linarith only [h102, h125, hlam]
                              · linarith only [h124, hlam, p106_0]
                            · linarith only [h1, h101, h104, h123, h99, hlam]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p106_1, u5ehi8]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht12, p106_1, u1ehi2]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [hc23, hlam, hphi, ht12, p106_1, u1ehi2]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            rcases p106_3 (m.d 0 3) (by simp) with h138 | h138
                            · linarith only [h138, h3, hlam]
                            · linarith only [h1, h101, h104, h138, h99, hlam]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            rcases p106_3 (m.d 0 3) (by simp) with h141 | h141
                            · linarith only [h141, h3, hlam]
                            · linarith only [h141, h96, hlam]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h1, h101, h104, h99, hlam, p106_1]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h99, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h102, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h104, hlam, p106_1]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h96, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h100, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [h103, hlam, p106_0]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [hc34, hlam, hphi, ht45, p106_1, u5elo3]
                          · have p106_0 := h106c.1
                            have p106_1 := h106c.2.1
                            have p106_2 := h106c.2.2.1
                            have p106_3 := h106c.2.2.2
                            linarith only [hlam, p106_0]
                      · linarith only [h0, h100, h103, h2, h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo0]
                    · linarith only [h0, h102, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h101, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h100, h99, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                    · linarith only [h158, h160, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · linarith only [h0, h160, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h158, h159, h99, hlam, hphi, u5ehi8, u5elo4]
                · linarith only [h158, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
          · linarith only [h1, h96, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h168 | h168
    · linarith only [h0, h168, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h170 | h170
      · linarith only [h0, h170, hc12, hlam, hphi, u1ehi4]
      · linarith only [h170, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_13_24_L_R_H_R (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · linarith only [h4, h5, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h8, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h12, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h12, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h15, h17, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h19, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h19, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
            · linarith only [h22, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                · linarith only [h1, h25, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                  · linarith only [h25, h27, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h24, h27, h4, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                · linarith only [h1, h30, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h30, h32, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h2, h34, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h34, hc45, hlam, hphi, u4ehi1]
        · linarith only [h3, hc45, hlam, hphi, u4ehi0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
        · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
          · linarith only [h0, h2, h39, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
            · linarith only [h1, h2, h39, h41, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                · linarith only [h1, h2, h41, h44, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h1, h2, h44, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                · linarith only [h1, h47, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h1, h2, h47, hc34, hlam, hphi, u3ehi1]
        · linarith only [h38, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
      · linarith only [h1, h51, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
        · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
          · linarith only [h0, h1, h54, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
            · linarith only [h0, h1, h54, h56, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
              · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
                · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                    · linarith only [h0, h51, h54, h58, h59, h61, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h51, h53, h61, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h51, h53, h59, h60, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · linarith only [h0, h1, h58, h59, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                · rcases m.htr 1 3 5 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                            · linarith only [h66, h72, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h53, h72, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h51, h53, h54, h66, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h51, h53, h54, h66, h70, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h51, h53, h54, h66, h69, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h51, h53, h68, hlam]
                  · linarith only [h51, h53, h66, h67, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · linarith only [h0, h1, h66, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h53, hc45, hlam, hphi, u4ehi0]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h82 | h82
    · rcases m.htr 0 1 4 (by decide) (by decide) with h83 | h83
      · linarith only [h0, h83, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h85 | h85
        · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
          · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                · linarith only [h82, h83, h87, h89, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h82, h83, h89, hc34, hlam, hphi, u3ehi1]
              · linarith only [h87, h88, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h0, h82, h86, h87, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h82, h86, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h85, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h96 | h96
      · linarith only [h0, h96, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h98 | h98
        · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
          · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
            · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                      · linarith only [h105, h99, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                        · linarith only [h105, h107, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                          · linarith only [h102, h105, h109, h99, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h109, h98, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h104, h96, h98, hlam]
                  · linarith only [h102, h103, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h102, h114, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                      · linarith only [h102, h117, h82, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                        · linarith only [h114, h119, h99, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h100, h121, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h102, h121, h96, h98, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h116, h96, h98, hlam]
              · linarith only [h100, h101, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
              · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                · linarith only [h100, h127, h99, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                  · linarith only [h127, h129, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                      · linarith only [h100, h127, h132, h96, h99, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h100, h132, h99, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h131, h96, h98, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                · linarith only [h100, h136, h99, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
                  · linarith only [h136, h138, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                      · linarith only [h136, h141, h82, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h100, h141, h99, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h140, h96, h98, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
            · linarith only [h145, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
              · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h153 | h153
                          · linarith only [h145, h147, h151, h153, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h145, h147, h152, h153, h98, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h148, h152, h96, h98, h99, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h148, h151, h96, h98, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h150, h96, h98, hlam]
                  · linarith only [h148, h149, h96, h98, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                  · linarith only [h148, h160, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h147, h160, h99, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h168 | h168
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h169 | h169
                            · linarith only [h163, h169, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h169, h98, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h163, h168, h96, h98, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h164, h167, h99, hlam]
                      · linarith only [h164, h166, h99, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h165, h96, h98, hlam]
                  · linarith only [h163, h164, h96, h98, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h177 | h177
                  · linarith only [h163, h177, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h179 | h179
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                      · linarith only [h163, h180, h82, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h180, h99, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h179, h96, h98, hlam]
        · linarith only [h98, hc45, hlam, hphi, u4ehi0]

theorem r1l7_14_25_L_0_H_R (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
              · linarith only [h3, h4, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                · linarith only [h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h11, h3, h4, h9, hc34, hlam, hphi, u4elo4]
                  · linarith only [h11, h3, h4, h6, h9, hc23, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
              · linarith only [h14, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                · linarith only [h16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h16, h18, h3, h6, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h14, h20, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h16, h18, h22, h6, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h22, h3, h4, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
          · linarith only [h25, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
              · linarith only [h1, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                · linarith only [h30, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                      · linarith only [h30, h34, hc14, hlam, hphi, u4elo2]
                      · linarith only [h27, h28, h33, h34, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                      · linarith only [h37, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                        · linarith only [h27, h3, h33, h37, h39, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h27, h28, h39, hc34, hlam, hphi, u4elo4]
                  · linarith only [h27, h28, h32, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
              · linarith only [h27, h43, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                · linarith only [h45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                      · linarith only [h27, h45, h49, hc13, hlam, hphi, ht34, u4elo2]
                      · linarith only [h27, h3, h47, h49, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h27, h3, h47, h48, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h3, h47, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
        · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
          · linarith only [h0, h2, h55, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
            · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
              · linarith only [h1, h2, h55, h58, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h0, h2, h54, h58, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
              · linarith only [h0, h2, h54, h55, h57, h61, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, u4elo3, u5ehi3]
              · linarith only [h0, h2, h54, h61, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
          · linarith only [h1, h54, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
            · rcases m.htr 1 3 5 (by decide) (by decide) with h67 | h67
              · linarith only [h1, h2, h64, h67, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                · linarith only [h1, h2, h66, h67, h69, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · linarith only [h1, h2, h66, h69, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h72 | h72
              · linarith only [h66, h72, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                · linarith only [h74, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · linarith only [h0, h2, h74, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h77 | h77
      · linarith only [h1, h77, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
        · linarith only [h0, h1, h79, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
          · linarith only [h0, h1, h79, h81, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
            · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
              · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                · linarith only [h85, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · linarith only [h0, h77, h85, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · linarith only [h0, h1, h84, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h0, h1, h83, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h90 | h90
    · rcases m.htr 0 1 5 (by decide) (by decide) with h91 | h91
      · linarith only [h0, h91, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
        · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
          · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
            · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
              · linarith only [h90, h91, h94, h96, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                · linarith only [h90, h91, h95, h96, h98, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · linarith only [h90, h91, h95, h98, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h101 | h101
              · linarith only [h101, h95, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                · linarith only [h103, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · linarith only [h103, h90, h91, hc13, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
            · linarith only [h0, h106, h90, h94, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
              · linarith only [h0, h108, h90, h94, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                · linarith only [h0, h110, h90, h93, h94, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, u4elo1, u5ehi4]
                · linarith only [h0, h110, h90, h93, h94, hc23, hlam, hphi, ht34, u4elo4]
        · linarith only [h0, h90, h93, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h114 | h114
      · linarith only [h0, h114, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
        · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
          · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
            · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
              · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                · linarith only [h120, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                    · linarith only [h116, h123, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h119, h120, h122, h123, hc34, hlam, hphi, u4elo4]
                  · linarith only [h118, h120, h122, hc23, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                · linarith only [h127, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                    · linarith only [h116, h119, h127, h130, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h127, h132, hc14, hlam, hphi, u4elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                        · linarith only [h129, h134, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h119, h134, h90, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h118, h119, h129, hc23, hc35, hlam, hphi]
            · linarith only [h118, h90, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
              · linarith only [h116, h117, h140, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                · linarith only [h142, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                  · linarith only [h116, h117, h142, h144, hc34, hlam, hphi, u4elo4]
                  · linarith only [h116, h117, h139, h142, h144, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h139, h90, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
          · linarith only [h116, h148, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
            · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
              · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                · linarith only [h152, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                      · linarith only [h152, h156, hc14, hlam, hphi, u4elo2]
                      · linarith only [h0, h148, h156, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h116, h151, h155, hc01, hc13, hlam, hphi]
                  · linarith only [h116, h154, h90, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                · linarith only [h150, h151, h161, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h151, h164, h90, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h116, h164, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h116, h150, h163, hc01, hc13, hlam, hphi]
            · linarith only [h150, h90, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]

theorem r1l7_20_11_13_14_H_I_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
              · linarith only [h0, h4, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
              · linarith only [h5, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                · linarith only [h1, h11, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h11, h14, hc13, hlam, hphi, u3elo2]
                    · linarith only [h14, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                    · linarith only [h11, h17, hc13, hlam, hphi, u3elo2]
                    · linarith only [h17, h5, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
            · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
              · linarith only [h0, h21, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                · linarith only [h1, h23, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                    · linarith only [h20, h23, h26, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h20, h26, h4, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h20, h29, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                    · linarith only [h0, h20, h29, h4, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
              · linarith only [h20, h32, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                · linarith only [h1, h34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                    · linarith only [h20, h34, h37, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h20, h37, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                    · linarith only [h34, h40, hc13, hlam, hphi, u3elo2]
                    · linarith only [h20, h40, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 2 4 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h2, h45, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
            · linarith only [h0, h2, h47, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
              · linarith only [h1, h2, h45, h47, h49, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                · linarith only [h1, h2, h51, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                · linarith only [h1, h2, h47, h51, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h54 | h54
          · linarith only [h0, h2, h54, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
            · linarith only [h0, h2, h56, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
              · linarith only [h1, h2, h54, h56, h58, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                · linarith only [h1, h2, h60, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                · linarith only [h1, h2, h56, h60, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
    · rcases m.htr 0 1 4 (by decide) (by decide) with h65 | h65
      · linarith only [h0, h65, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h67 | h67
        · rcases m.htr 0 2 4 (by decide) (by decide) with h68 | h68
          · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
            · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                · linarith only [h64, h65, h70, h71, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                · linarith only [h64, h65, h69, h71, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h64, h68, h69, h70, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h69, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
              · linarith only [h0, h64, h68, h76, h77, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                · linarith only [h64, h79, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                · linarith only [h0, h64, h77, h79, hc13, hlam, hphi, u3elo3]
            · linarith only [h0, h64, h76, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h83 | h83
          · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
            · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
              · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                · linarith only [h64, h67, h86, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi3]
                · linarith only [h64, h65, h86, hc13, hlam, hphi, u3elo3]
              · linarith only [h0, h64, h83, h85, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h64, h84, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
            · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
              · linarith only [h0, h64, h83, h91, h92, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                · linarith only [h64, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                · linarith only [h0, h64, h92, h94, hc13, hlam, hphi, u3elo3]
            · linarith only [h0, h64, h91, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h98 | h98
      · linarith only [h0, h98, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h100 | h100
        · rcases m.htr 0 2 4 (by decide) (by decide) with h101 | h101
          · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
            · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
              · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                    · linarith only [h102, h106, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                    · linarith only [h104, h106, hc23, hlam, hphi, u3elo1]
                  · linarith only [h104, h105, h98, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h100, h104, h64, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h0, h100, h101, h103, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h101, h102, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
            · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
              · linarith only [h0, h100, h101, h114, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                · linarith only [h113, h114, h116, hlam]
                · linarith only [h100, h116, h64, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
            · linarith only [h0, h100, h113, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                    · linarith only [h121, h125, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                    · linarith only [h123, h125, hc23, hlam, hphi, u3elo1]
                  · linarith only [h123, h124, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                · linarith only [h123, h64, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h120, h122, hlam]
            · linarith only [h0, h121, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
            · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
              · linarith only [h0, h120, h133, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                · linarith only [h132, h133, h135, hlam]
                · linarith only [h135, h64, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h132, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_11_13_14_H_L_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h1, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h12, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
            · linarith only [h0, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h1, h15, h3, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h1, h2, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h19 | h19
      · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
        · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
            · linarith only [h1, h19, h22, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
              · linarith only [h0, h24, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h19, h24, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
            · linarith only [h0, h1, h19, h21, h27, hc23, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u3elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h29, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1, h19, h21, h29, hc12, hlam, hphi, ht23, u3elo4]
        · linarith only [h1, h19, h20, hc24, hlam, hphi, u4elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
        · rcases m.htr 0 3 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
            · linarith only [h0, h1, h35, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
              · linarith only [h0, h19, h37, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                        · linarith only [h33, h43, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h42, h43, hc34, hlam, hphi, u4elo2]
                      · linarith only [h0, h19, h42, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h1, h34, h41, hlam]
                  · linarith only [h0, h1, h40, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h34, h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
            · linarith only [h0, h1, h50, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
              · linarith only [h0, h19, h52, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                · linarith only [h34, h54, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                    · linarith only [h54, h57, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h1, h57, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h0, h1, h33, h56, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
          · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h1, h62, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
              · linarith only [h0, h19, h64, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                  · linarith only [h33, h61, h67, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1, h67, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h61, h66, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
            · linarith only [h0, h1, h71, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
              · linarith only [h0, h19, h73, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
                · linarith only [h1, h61, h75, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h1, h33, h77, hc02, hlam, hphi, ht23, u3elo2]
                  · linarith only [h0, h1, h77, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h80 | h80
    · rcases m.htr 0 2 4 (by decide) (by decide) with h81 | h81
      · rcases m.htr 0 3 4 (by decide) (by decide) with h82 | h82
        · rcases m.htr 0 3 5 (by decide) (by decide) with h83 | h83
          · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
            · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
              · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                  · linarith only [h80, h87, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h82, h87, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h80, h83, h86, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h81, h85, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h84, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
            · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
              · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                · linarith only [h82, h83, h95, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h80, h97, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h82, h97, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h81, h94, hlam]
            · linarith only [h0, h93, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h102 | h102
          · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
            · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
              · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                  · linarith only [h106, h80, h82, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h108, h80, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h102, h108, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h102, h105, h82, hc13, hlam, hphi, ht34, u4elo3]
              · linarith only [h0, h104, h81, hlam]
            · linarith only [h0, h103, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
            · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
              · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                · linarith only [h102, h116, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                  · linarith only [h118, h80, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h116, h118, h120, h81, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h122 | h122
                      · linarith only [h122, h81, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                        · linarith only [h118, h122, h124, hc23, hlam, hphi, u3elo3]
                        · linarith only [h124, h80, h82, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h115, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h114, h80, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h80, h81, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h130 | h130
      · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
        · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
          · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
            · linarith only [h130, h133, h80, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · linarith only [h0, h133, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
            · linarith only [h130, h136, h80, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · linarith only [h0, h136, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h130, h131, h80, hc24, hlam, hphi, u4elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h140 | h140
        · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
          · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
            · linarith only [h0, h142, h80, hc01, hlam, hphi, u1elo1]
            · linarith only [h0, h142, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
            · linarith only [h0, h145, h80, hc01, hlam, hphi, u1elo1]
            · linarith only [h0, h145, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h148 | h148
          · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
            · linarith only [h0, h149, h80, hc01, hlam, hphi, u1elo1]
            · linarith only [h0, h149, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
            · linarith only [h0, h152, h80, hc01, hlam, hphi, u1elo1]
            · linarith only [h0, h152, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_11_13_14_H_L_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h1, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · linarith only [h0, h1, h6, h7, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h10 | h10
            · linarith only [h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · linarith only [h1, h10, h3, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h13 | h13
        · linarith only [h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h15, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
            · linarith only [h17, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
              · linarith only [h17, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h1, h13, h19, h21, h22, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h15, h19, h21, h24, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                      · linarith only [h0, h1, h17, h22, h26, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h26, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h29, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h1, h17, h21, h31, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                      · linarith only [h0, h1, h17, h29, h33, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h33, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h36 | h36
    · linarith only [h36, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h38 | h38
      · rcases m.htr 0 2 3 (by decide) (by decide) with h39 | h39
        · linarith only [h39, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
          · rcases m.htr 0 3 4 (by decide) (by decide) with h42 | h42
            · linarith only [h42, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · linarith only [h0, h38, h39, h42, hlam]
          · linarith only [h0, h38, h41, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h46 | h46
        · linarith only [h46, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h48 | h48
          · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
            · linarith only [h49, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · linarith only [h46, h48, h49, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
            · linarith only [h52, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h54 | h54
              · linarith only [h52, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h56 | h56
                · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                        · linarith only [h52, h57, h60, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h46, h59, h60, hc01, hc13, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                        · linarith only [h36, h59, h63, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h54, h57, h59, h65, hc34, hlam, hphi, u3ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
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
                                linarith only [h38, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h48, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h52, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hc45, hlam, hphi, ht0b, ht5b, p68_1, u0elo3]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h52, h59, hc34, hlam, hphi, p68_1, u3ehi0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h59, h63, hc34, hlam, hphi, p68_1, u3ehi2]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h59, hlam, p68_1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                rcases p68_3 (m.d 0 4) (by simp) with h78 | h78
                                · linarith only [h38, h78, hlam]
                                · linarith only [h56, h78, hlam]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h54, h56, h58, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p68_1, u3ehi0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h58, hlam, p68_1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h63, hlam, p68_1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                rcases p68_3 (m.d 0 4) (by simp) with h85 | h85
                                · linarith only [h48, h85, hlam]
                                · linarith only [h56, h85, hlam]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h54, h56, hc34, hlam, hphi, p68_1, u3ehi0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h38, hc01, hc34, hlam, hphi, ht12, ht23, p68_1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h48, hc01, hc34, hlam, hphi, ht12, ht23, p68_1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                rcases p68_3 (m.d 0 4) (by simp) with h92 | h92
                                · linarith only [h52, h92, hlam]
                                · linarith only [h56, h92, hlam]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h56, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h59, hc45, hlam, hphi, ht34, p68_1, u3ehi1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h46, h56, h63, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p68_1, u0elo3]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h67, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                            · linarith only [h56, h67, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h46, h57, h58, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
                    · linarith only [h0, h102, h48, h57, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                            · rcases h4bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h38, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h48, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h52, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hc45, hlam, hphi, ht0b, ht5b, p108_1, u0elo3]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 4) (by simp) with h114 | h114
                                · linarith only [h114, h38, hlam]
                                · rcases p108_3 (m.d 1 4) (by simp) with h116 | h116
                                  · rcases p108_3 (m.d 2 4) (by simp) with h117 | h117
                                    · rcases p108_3 (m.d 3 4) (by simp) with h118 | h118
                                      · linarith only [h104, h118, hlam]
                                      · linarith only [h118, h52, hlam]
                                    · linarith only [h117, h48, hlam]
                                  · linarith only [h116, h38, hlam]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h102, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h102, h105, h107, h54, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p108_1, u3ehi0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 4) (by simp) with h126 | h126
                                · linarith only [h126, h38, hlam]
                                · linarith only [h126, h56, hlam]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 4) (by simp) with h129 | h129
                                · linarith only [h129, h48, hlam]
                                · rcases p108_3 (m.d 1 4) (by simp) with h131 | h131
                                  · linarith only [h102, h131, hlam]
                                  · linarith only [h131, h38, hlam]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h105, h38, hc01, hc23, hlam, hphi, ht12, p108_1]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h105, h107, h54, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p108_1, u3ehi0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 4) (by simp) with h137 | h137
                                · linarith only [h137, h48, hlam]
                                · linarith only [h137, h56, hlam]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h52, hc34, hlam, hphi, p108_1, u3ehi0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h104, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h105, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 4) (by simp) with h144 | h144
                                · linarith only [h144, h52, hlam]
                                · linarith only [h144, h56, hlam]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h56, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h104, hc45, hlam, hphi, ht34, p108_1, u3ehi3]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h56, hc24, hlam, hphi, ht0b, ht45, ht5b, p108_1, u0elo3]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h107, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                            · linarith only [h107, h56, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h0, h106, h57, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h104, h105, h57, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                        · linarith only [h104, h155, h36, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h155, h57, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                        · linarith only [h158, h161, h52, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h160, h161, h46, hc01, hc13, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                        · linarith only [h160, h164, h36, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                          · linarith only [h158, h160, h166, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                            · linarith only [h168, h52, h56, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h160, h168, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h0, h158, h159, h46, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                    · linarith only [h0, h158, h172, h48, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                            · linarith only [h158, h174, h177, h52, h56, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h177, h52, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h0, h172, h175, h176, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h158, h174, h175, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                        · linarith only [h174, h182, h36, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h158, h182, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
