import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_R_L_R_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h11, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h14, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h8, h9, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, h2, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                        · linarith only [h21, h8, hc23, hlam, hphi, ht12, u1ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                          · linarith only [h18, h23, h6, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                              · rcases h4bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 4) (by simp) with h29 | h29
                                  · rcases p27_3 (m.d 1 4) (by simp) with h30 | h30
                                    · linarith only [h1, h30, hlam]
                                    · rcases p27_3 (m.d 2 4) (by simp) with h32 | h32
                                      · linarith only [h3, h32, hlam]
                                      · rcases p27_3 (m.d 3 4) (by simp) with h34 | h34
                                        · linarith only [h34, h4, hlam]
                                        · linarith only [h34, h8, hlam]
                                  · linarith only [h1, h29, hlam]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 4) (by simp) with h38 | h38
                                  · rcases p27_3 (m.d 1 4) (by simp) with h39 | h39
                                    · linarith only [h1, h39, hlam]
                                    · linarith only [h39, h7, hlam]
                                  · linarith only [h3, h38, hlam]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h2, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p27_1, u1ehi2]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 4) (by simp) with h44 | h44
                                  · rcases p27_3 (m.d 1 4) (by simp) with h45 | h45
                                    · linarith only [h1, h45, hlam]
                                    · linarith only [h20, h45, hlam]
                                  · linarith only [h44, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h1, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h1, h25, hc01, hc45, hlam, hphi, ht0b, ht5b, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h8, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 4) (by simp) with h53 | h53
                                  · rcases p27_3 (m.d 1 4) (by simp) with h54 | h54
                                    · rcases p27_3 (m.d 2 4) (by simp) with h55 | h55
                                      · linarith only [h55, h7, hlam]
                                      · linarith only [h25, h55, hlam]
                                    · linarith only [h54, hlam, p27_0]
                                  · linarith only [h5, h53, hlam]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h3, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h7, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h21, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h4, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p27_1, u1ehi3]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h2, h21, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 4) (by simp) with h69 | h69
                                  · rcases p27_3 (m.d 1 4) (by simp) with h70 | h70
                                    · linarith only [h70, h8, hlam]
                                    · linarith only [h20, h70, hlam]
                                  · linarith only [h5, h69, hlam]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h5, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h20, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h25, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h26, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                              · linarith only [h0, h2, h26, h4, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                            · linarith only [h1, h20, h21, h25, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                        · linarith only [h0, h6, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                          · linarith only [h18, h83, hc23, hlam, hphi, ht12, u1ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                            · linarith only [h20, h7, h85, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                              · linarith only [h20, h87, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h0, h2, h4, h5, h8, h87, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · linarith only [h0, h3, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h93 | h93
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                        · linarith only [h0, h2, h6, h91, h95, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h6, h91, h92, h95, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                        · linarith only [h0, h2, h6, h91, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h6, h98, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h92, h93, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h6, h91, h92, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                              · rcases h4bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  rcases p110_3 (m.d 0 4) (by simp) with h112 | h112
                                  · rcases p110_3 (m.d 1 4) (by simp) with h113 | h113
                                    · linarith only [h1, h113, hlam]
                                    · rcases p110_3 (m.d 2 4) (by simp) with h115 | h115
                                      · linarith only [h115, h3, hlam]
                                      · linarith only [h115, h91, hlam]
                                  · linarith only [h1, h112, hlam]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h0, h2, h4, h91, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p110_1, u1ehi1]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  rcases p110_3 (m.d 0 4) (by simp) with h120 | h120
                                  · rcases p110_3 (m.d 1 4) (by simp) with h121 | h121
                                    · linarith only [h1, h121, hlam]
                                    · linarith only [h103, h121, hlam]
                                  · linarith only [h120, h4, hlam]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  rcases p110_3 (m.d 0 4) (by simp) with h125 | h125
                                  · rcases p110_3 (m.d 1 4) (by simp) with h126 | h126
                                    · linarith only [h1, h126, hlam]
                                    · linarith only [h105, h126, hlam]
                                  · linarith only [h125, hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h1, hlam, p110_1]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h91, hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h1, h109, hc01, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  rcases p110_3 (m.d 0 4) (by simp) with h134 | h134
                                  · rcases p110_3 (m.d 1 4) (by simp) with h135 | h135
                                    · rcases p110_3 (m.d 2 4) (by simp) with h136 | h136
                                      · rcases p110_3 (m.d 3 4) (by simp) with h137 | h137
                                        · linarith only [h103, h137, hlam]
                                        · linarith only [h109, h137, hlam]
                                      · linarith only [h108, h136, hlam]
                                    · linarith only [h135, hlam, p110_0]
                                  · linarith only [h134, h5, hlam]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h3, hlam, p110_1]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h106, hc23, hlam, hphi, ht12, p110_1, u1ehi3]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h0, h106, h109, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p110_1, u3ehi4]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  rcases p110_3 (m.d 0 4) (by simp) with h147 | h147
                                  · rcases p110_3 (m.d 1 4) (by simp) with h148 | h148
                                    · linarith only [h148, h91, hlam]
                                    · linarith only [h105, h148, hlam]
                                  · linarith only [h147, h5, hlam]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h4, hlam, p110_1]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h103, hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h106, hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [hlam, p110_0]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h0, h103, h2, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p110_1]
                                · have p110_0 := h110c.1
                                  have p110_1 := h110c.2.1
                                  have p110_2 := h110c.2.2.1
                                  have p110_3 := h110c.2.2.2
                                  linarith only [h5, hlam, p110_0]
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
                              · linarith only [h1, h105, h109, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h105, h108, h91, hlam]
                          · linarith only [h107, h6, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h106, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h168 | h168
                            · linarith only [h105, h166, h168, h91, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h168, h2, h4, h5, h91, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · linarith only [h104, h167, h6, hlam]
                        · linarith only [h0, h103, h105, h166, h2, h4, h5, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h103, h104, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                    · linarith only [h0, h103, h174, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                        · linarith only [h103, h177, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h0, h177, h2, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                        · linarith only [h0, h103, h180, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h180, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc24, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc14, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_11_13_14_M_LI_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h3, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                  · linarith only [h0, h10, h3, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h10, h3, h4, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h3, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                  · linarith only [h13, h3, h4, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
              · linarith only [h1, h16, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                · linarith only [h18, h3, h6, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h16, h20, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h20, h3, h4, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
          · linarith only [h23, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
            · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
              · linarith only [h1, h26, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                  · linarith only [h26, h29, h3, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h25, h29, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h25, h28, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
              · linarith only [h1, h33, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                  · linarith only [h33, h36, hc13, hlam, hphi, u3elo2]
                  · linarith only [h3, h36, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                  · linarith only [h3, h33, h39, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h3, h39, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
        · linarith only [h0, h2, h42, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
          · linarith only [h1, h2, h42, h44, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
            · linarith only [h1, h2, h42, h46, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
              · linarith only [h1, h2, h48, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                · linarith only [h1, h2, h50, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · linarith only [h1, h2, h42, h50, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h54 | h54
    · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
      · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
        · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
          · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
            · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
              · linarith only [h54, h59, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
                · linarith only [h0, h54, h61, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                  · linarith only [h0, h55, h56, h59, h61, h63, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                    · linarith only [h56, h61, h65, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                      · linarith only [h57, h67, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                      · linarith only [h0, h55, h58, h67, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
            · linarith only [h0, h55, h58, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
              · linarith only [h54, h72, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · linarith only [h0, h54, h56, h57, h72, hc23, hlam, hphi, u3elo3]
            · linarith only [h0, h55, h71, hlam]
        · linarith only [h0, h56, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
        · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
          · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
            · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
              · linarith only [h54, h55, h79, h80, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                · linarith only [h54, h55, h79, h82, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · linarith only [h54, h55, h77, h82, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
              · linarith only [h54, h85, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h54, h79, h87, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h54, h79, h87, hc13, hlam, hphi, u3elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
            · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
              · linarith only [h54, h55, h78, h90, h91, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h54, h55, h77, h78, h90, h91, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
              · linarith only [h0, h54, h78, h94, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h54, h77, h78, h94, hc23, hlam, hphi, u3elo3]
        · linarith only [h0, h77, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h98 | h98
      · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
        · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
          · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
            · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h99, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                  · linarith only [h102, h104, hc23, hlam, hphi, u3elo1]
                · linarith only [h102, h103, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
              · linarith only [h101, h102, h54, h98, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
            · linarith only [h0, h101, h54, h98, hc02, hlam, hphi, ht23, u3elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
              · linarith only [h100, h111, h99, hlam]
              · linarith only [h111, h54, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h110, h54, h98, h99, hlam]
        · linarith only [h0, h98, h99, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
        · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
          · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
            · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
              · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                  · linarith only [h116, h121, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                  · linarith only [h119, h121, hc23, hlam, hphi, u3elo1]
                · linarith only [h119, h120, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
              · linarith only [h119, h54, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
              · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                · linarith only [h116, h118, h127, hlam]
                · linarith only [h127, h54, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · linarith only [h126, h54, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
            · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
              · linarith only [h116, h117, h132, hlam]
              · linarith only [h132, h54, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
              · linarith only [h116, h117, h135, hlam]
              · linarith only [h135, h54, hc01, hlam, hphi, ht12, ht23, u3elo3]
        · linarith only [h0, h116, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_11_13_14_M_LR_L_0_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h1, h8, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                  · linarith only [h1, h4, h8, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h1, h11, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                  · linarith only [h1, h11, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                  · linarith only [h1, h15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                  · linarith only [h1, h15, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h1, h18, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                  · linarith only [h1, h18, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
            · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h22 | h22
            · linarith only [h22, h4, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h22, h28, hlam, hphi, ht01, u0ehi7, u1elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                        · linarith only [h31, h4, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · linarith only [h0, h25, h31, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · linarith only [h0, h24, h26, h3, h30, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                  · linarith only [h35, h4, hlam, hphi, ht01, u0ehi7, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h22, h37, hlam, hphi, ht01, u0ehi7, u1elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                        · linarith only [h4, h40, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                          · rcases h4bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h0, h3, h37, h39, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43_1, u1elo0, u3ehi1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h0, h25, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p43_1, u1elo0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h4, hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              rcases p43_3 (m.d 0 4) (by simp) with h48 | h48
                              · rcases p43_3 (m.d 1 4) (by simp) with h49 | h49
                                · linarith only [h2, h49, hlam]
                                · linarith only [h39, h49, hlam]
                              · linarith only [h48, hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h2, hlam, p43_1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h25, hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h35, hlam, p43_1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p43_1, u1elo0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h3, hlam, p43_1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h0, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p43_1, u1elo0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h40, hlam, p43_1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h0, h3, hc45, hlam, hphi, ht01, ht0b, ht5b, p43_1, u1elo0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h0, h25, h3, hc12, hc34, hlam, hphi, ht01, ht23, p43_1, u0ehi8, u1elo0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h37, h39, hc34, hlam, hphi, p43_1, u3ehi1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h25, h37, h39, hc34, hlam, hphi, p43_1, u3ehi1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              rcases p43_3 (m.d 0 4) (by simp) with h67 | h67
                              · linarith only [h4, h67, hlam]
                              · linarith only [h24, h67, hlam]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h24, hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h39, hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h25, h37, h39, hc45, hlam, hphi, ht34, p43_1, u3ehi1]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [h42, hlam, p43_0]
                            · have p43_0 := h43c.1
                              have p43_1 := h43c.2.1
                              have p43_2 := h43c.2.2.1
                              have p43_3 := h43c.2.2.2
                              linarith only [hlam, p43_0]
                          · linarith only [h0, h25, h3, h39, h42, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h0, h24, h3, h35, h39, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                  · linarith only [h4, h78, hlam, hphi, ht01, u0ehi7, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h22, h77, h78, h80, hlam, hphi, ht01, u0ehi7, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                      · linarith only [h0, h24, h77, h82, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                        · linarith only [h4, h84, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · linarith only [h0, h77, h84, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                  · linarith only [h4, h87, hlam, hphi, ht01, u0ehi7, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h0, h22, h3, h77, h87, h89, hlam, hphi, ht01, u0ehi7, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                      · linarith only [h0, h24, h3, h4, h77, h91, hlam, hphi, ht01, u0ehi7, u1elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                        · linarith only [h0, h3, h4, h77, h93, hc12, hc23, hlam, hphi, ht01, u0ehi7, u1elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h95 | h95
                          · linarith only [h0, h24, h3, h4, h77, h95, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi7, u1elo0]
                          · linarith only [h0, h3, h4, h77, h87, h95, hc45, hlam, hphi, ht01, ht34, u0ehi7, u1elo0, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
          · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
            · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h3, hlam, hphi, ht01, u0ehi6, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h1, h103, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                  · linarith only [h1, h103, h98, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                · linarith only [h106, h3, hlam, hphi, ht01, u0ehi6, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                  · linarith only [h1, h108, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                  · linarith only [h1, h108, h98, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
            · linarith only [h98, h99, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
            · linarith only [h112, h98, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                · linarith only [h115, h3, hlam, hphi, ht01, u0ehi6, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                  · linarith only [h117, h98, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h112, h117, h119, h2, hlam, hphi, ht01, u0ehi7, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                        · linarith only [h122, h98, hc23, hlam, hphi, ht01, ht12, u0ehi7]
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
                              linarith only [h119, h121, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p125_1, u1elo0, u3ehi1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h3, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h98, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              rcases p125_3 (m.d 0 4) (by simp) with h130 | h130
                              · rcases p125_3 (m.d 1 4) (by simp) with h131 | h131
                                · linarith only [h131, h2, hlam]
                                · linarith only [h121, h131, hlam]
                              · linarith only [h130, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h2, hlam, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h115, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h117, hlam, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p125_1, u1elo0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p125_1, u0ehi8]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h117, h122, hc34, hlam, hphi, p125_1, u3ehi1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h122, hlam, p125_1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              rcases p125_3 (m.d 0 4) (by simp) with h144 | h144
                              · linarith only [h144, h3, hlam]
                              · linarith only [h114, h144, hlam]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h112, h114, hc34, hlam, hphi, ht01, ht12, ht23, p125_1, u0ehi7]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h119, h121, hc34, hlam, hphi, p125_1, u3ehi1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h119, h121, h2, h3, hc34, hlam, hphi, ht01, p125_1, u0ehi6, u1elo0, u3ehi1]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              rcases p125_3 (m.d 0 4) (by simp) with h151 | h151
                              · linarith only [h151, h98, hlam]
                              · linarith only [h114, h151, hlam]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h114, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h121, hlam, p125_0]
                            · have p125_0 := h125c.1
                              have p125_1 := h125c.2.1
                              have p125_2 := h125c.2.2.1
                              have p125_3 := h125c.2.2.2
                              linarith only [h119, h121, h2, h3, hc45, hlam, hphi, ht01, ht34, p125_1, u0ehi6, u1elo0, u3ehi1]
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
                          · linarith only [h121, h122, h124, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · linarith only [h114, h117, h121, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
                · linarith only [h161, h3, hlam, hphi, ht01, u0ehi6, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                  · linarith only [h163, h98, hlam, hphi, ht01, u0ehi7, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h165 | h165
                    · linarith only [h112, h163, h165, h2, hlam, hphi, ht01, u0ehi7, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
                      · linarith only [h114, h167, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                        · linarith only [h169, h98, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h171 | h171
                          · linarith only [h114, h171, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h169, h171, hc45, hlam, hphi, ht34, u3ehi2]
      · linarith only [h2, hlam, hphi, ht01, u0ehi5, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem r1l7_20_11_13_14_M_LR_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h0, h1, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h0, h1, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h0, h1, h12, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
            · linarith only [h0, h15, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h0, h1, h15, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
        · linarith only [h1, h18, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
          · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h21, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h1, h2, h21, hc12, hc24, hlam, hphi]
          · linarith only [h1, h2, h20, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h25 | h25
      · rcases m.htr 0 3 4 (by decide) (by decide) with h26 | h26
        · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
            · linarith only [h1, h25, h27, h28, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h30, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · linarith only [h1, h25, h30, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
            · linarith only [h1, h25, h33, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
              · linarith only [h0, h35, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · linarith only [h1, h25, h35, hc12, hc23, hlam, hphi]
        · linarith only [h1, h25, h26, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h39 | h39
        · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
            · linarith only [h1, h41, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
              · linarith only [h0, h25, h43, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                      · linarith only [h39, h48, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                      · linarith only [h40, h48, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                    · linarith only [h25, h39, h40, h47, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h25, h45, h46, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h45, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
            · linarith only [h0, h1, h54, hlam, hphi, u0ehi6, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
              · linarith only [h0, h25, h56, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h40, h58, h60, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                    · linarith only [h25, h60, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                  · linarith only [h1, h59, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h39, h58, hlam, hphi, u0ehi6, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
          · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
            · linarith only [h0, h1, h66, hlam, hphi, u0ehi6, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
              · linarith only [h0, h25, h68, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                · linarith only [h39, h70, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                · linarith only [h1, h70, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
            · linarith only [h0, h1, h73, hlam, hphi, u0ehi6, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
              · linarith only [h0, h25, h75, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                · linarith only [h1, h39, h77, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · linarith only [h1, h77, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h80 | h80
    · rcases m.htr 0 2 4 (by decide) (by decide) with h81 | h81
      · rcases m.htr 0 3 4 (by decide) (by decide) with h82 | h82
        · rcases m.htr 0 4 5 (by decide) (by decide) with h83 | h83
          · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
            · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
              · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                · linarith only [h80, h86, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h82, h86, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
              · linarith only [h0, h81, h85, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h84, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
            · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
              · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                · linarith only [h80, h93, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                · linarith only [h80, h82, h93, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
              · linarith only [h0, h81, h92, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h91, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h98 | h98
          · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
              · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h80, h82, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h101, h103, h81, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                    · linarith only [h105, h81, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                    · linarith only [h101, h105, h98, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
              · linarith only [h0, h100, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h99, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 2 4 (by decide) (by decide) with h111 | h111
              · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                · linarith only [h112, h80, h82, hlam, hphi, u0ehi7, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h112, h114, h81, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                    · linarith only [h116, h81, h98, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h118 | h118
                      · linarith only [h118, h82, h98, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                      · linarith only [h118, h82, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h0, h111, h81, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h110, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
        · linarith only [h123, h80, h81, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h125 | h125
          · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
            · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
              · linarith only [h127, h80, h81, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h127, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h126, h80, hlam, hphi, u0ehi5, u0elo1]
          · linarith only [h125, h80, h81, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h132 | h132
      · rcases m.htr 0 3 4 (by decide) (by decide) with h133 | h133
        · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
          · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
            · linarith only [h132, h134, h135, h80, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h0, h135, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
            · linarith only [h138, h80, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h138, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · linarith only [h132, h133, h80, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
        · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
          · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
            · linarith only [h144, h80, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h144, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
            · linarith only [h0, h147, h80, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h147, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
          · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
            · linarith only [h0, h151, h80, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h151, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
            · linarith only [h0, h154, h80, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h154, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_20_12_13_15_H_I_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h11, h13, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h11, h12, h13, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h12, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                        · linarith only [h11, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h10, h5, hc13, hlam, hphi, u3elo0]
                    · linarith only [h4, h5, h9, hlam, hphi, ht23, u2ehi1, u3elo0]
                  · linarith only [h8, hlam, hphi, ht23, u2ehi1, u3elo2]
                · linarith only [h4, h7, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h3, h6, hlam, hphi, ht23, u2ehi2, u3elo4]
            · linarith only [h3, h5, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · linarith only [h3, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
        · rcases m.htr 0 2 4 (by decide) (by decide) with h27 | h27
          · linarith only [h0, h2, h27, hlam]
          · linarith only [h26, h27, hc24, hlam, hphi, u2ehi2]
        · linarith only [h26, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
    · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
      · rcases m.htr 0 2 3 (by decide) (by decide) with h34 | h34
        · rcases m.htr 0 2 4 (by decide) (by decide) with h35 | h35
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36 | h36
            · rcases m.htr 0 3 5 (by decide) (by decide) with h37 | h37
              · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
                · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                            · linarith only [h0, h32, h39, h42, h44, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h32, h40, h41, h43, h44, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h43, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                        · linarith only [h42, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h36, h41, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h32, h39, h40, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h39, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h35, h38, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h35, h36, h37, hlam, hphi, ht23, u2ehi3, u3elo4]
            · linarith only [h34, h36, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h34, h35, hc24, hlam, hphi, u2ehi2]
        · linarith only [h34, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h57 | h57
        · rcases m.htr 0 2 4 (by decide) (by decide) with h58 | h58
          · rcases m.htr 0 3 4 (by decide) (by decide) with h59 | h59
            · linarith only [h32, h33, h59, hlam]
            · linarith only [h57, h59, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h57, h58, hc24, hlam, hphi, u2ehi2]
        · linarith only [h57, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
      · rcases m.htr 0 2 3 (by decide) (by decide) with h65 | h65
        · rcases m.htr 0 2 4 (by decide) (by decide) with h66 | h66
          · linarith only [h32, h64, h66, hlam, hphi, ht23, u2ehi3, u3elo1]
          · linarith only [h65, h66, hc24, hlam, hphi, u2ehi2]
        · linarith only [h65, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h70 | h70
        · rcases m.htr 0 2 4 (by decide) (by decide) with h71 | h71
          · rcases m.htr 0 3 4 (by decide) (by decide) with h72 | h72
            · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
              · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
                · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                            · rcases h0bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h32, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h64, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h64, h77, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p81_1, u3elo1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h70, h78, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h71, h79, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p81_1, u2ehi4]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                rcases p81_3 (m.d 0 1) (by simp) with h91 | h91
                                · linarith only [h0, h91, hlam]
                                · linarith only [h0, h91, hc01, hc12, hlam, hphi, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h32, hc01, hlam, hphi, ht12, ht23, p81_1, u3elo1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h70, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h32, h71, h79, hlam, hphi, ht23, p81_1, u2ehi4, u3elo1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h32, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p81_1, u3elo1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h64, h77, hc01, hlam, hphi, ht12, ht23, p81_1, u3elo1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h71, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h72, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h64, h77, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p81_1, u3elo1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p81_1, u5elo0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h64, h74, h77, hlam, hphi, ht23, p81_1, u2ehi0, u3elo1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h73, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h74, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                            · rcases h0bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h32, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h64, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, h70, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p109_1, u2ehi2]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, h64, hc01, hc12, hlam, hphi, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, h74, h80, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p109_1, u3elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h70, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h32, h71, h79, h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p109_1, u3elo1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h32, h74, h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p109_1, u3elo1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h64, hc01, hc14, hlam, hphi, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h71, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h72, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h32, h72, h74, h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p109_1, u3elo1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p109_1, u5elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h32, h70, h78, h79, h80, hc34, hlam, hphi, ht23, ht45, p109_1, u2ehi0, u3elo1, u5elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h73, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h74, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                          · linarith only [h79, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                        · linarith only [h78, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h32, h72, h77, hlam]
                    · linarith only [h0, h70, h76, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h70, h75, hlam]
                · linarith only [h71, h74, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h72, h73, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h70, h72, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h70, h71, hc24, hlam, hphi, u2ehi2]
        · linarith only [h70, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_15_H_I_L_R_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h12, hlam, hphi, ht23, u2ehi2, u3elo4]
                        · linarith only [h11, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h10, h4, h6, hlam, hphi, ht23, u2ehi1, u3elo0]
                    · linarith only [h9, hlam, hphi, ht23, u2ehi1, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h18, h21, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h21, hlam, hphi, ht23, u2ehi2, u3elo4]
                        · linarith only [h20, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h19, h4, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · linarith only [h18, hlam, hphi, ht23, u2ehi1, u3elo2]
                · linarith only [h3, h7, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h3, h6, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · linarith only [h3, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h32 | h32
        · rcases m.htr 0 2 4 (by decide) (by decide) with h33 | h33
          · rcases m.htr 0 2 5 (by decide) (by decide) with h34 | h34
            · linarith only [h0, h2, h34, hlam]
            · linarith only [h32, h34, hc25, hlam, hphi, u2ehi2]
          · linarith only [h32, h33, hc24, hlam, hphi, u2ehi2]
        · linarith only [h32, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h40 | h40
    · rcases m.htr 0 1 5 (by decide) (by decide) with h41 | h41
      · rcases m.htr 0 2 3 (by decide) (by decide) with h42 | h42
        · rcases m.htr 0 2 4 (by decide) (by decide) with h43 | h43
          · rcases m.htr 0 2 5 (by decide) (by decide) with h44 | h44
            · rcases m.htr 0 3 4 (by decide) (by decide) with h45 | h45
              · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                          · linarith only [h0, h40, h48, h51, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h51, hlam, hphi, ht23, u2ehi2, u3elo4]
                        · linarith only [h50, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h0, h40, h48, h49, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h48, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                          · linarith only [h0, h40, h57, h60, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h59, h60, hlam, hphi, ht23, u2ehi3, u3elo4]
                        · linarith only [h59, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h0, h44, h58, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h40, h46, h57, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h42, h46, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h42, h45, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h43, h44, hc25, hlam, hphi, u2ehi3]
          · linarith only [h42, h43, hc24, hlam, hphi, u2ehi2]
        · linarith only [h42, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h71 | h71
        · rcases m.htr 0 2 4 (by decide) (by decide) with h72 | h72
          · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
            · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
              · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
                · linarith only [h40, h41, h75, hlam]
                · linarith only [h71, h75, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h71, h74, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h71, h73, hc25, hlam, hphi, u2ehi2]
          · linarith only [h71, h72, hc24, hlam, hphi, u2ehi2]
        · linarith only [h71, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
      · linarith only [h40, h82, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h84 | h84
        · rcases m.htr 0 2 4 (by decide) (by decide) with h85 | h85
          · rcases m.htr 0 2 5 (by decide) (by decide) with h86 | h86
            · rcases m.htr 0 3 4 (by decide) (by decide) with h87 | h87
              · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                          · rcases h0bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h0, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h40, hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h40, h89, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo1, u5ehi4]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h82, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h0, h87, h89, hc12, hlam, hphi, ht01, ht0b, ht5b, p94_1, u5ehi4]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h0, h89, hc12, hlam, hphi, ht01, ht0b, ht5b, p94_1, u5ehi4]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p94_1, u5ehi0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, p94_1, u3elo0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h84, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h40, h89, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo1, u5ehi4]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h40, h86, hlam, hphi, ht23, p94_1, u2ehi4, u3elo1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h0, h85, hc01, hc12, hlam, hphi, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h85, hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h87, hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h40, h86, h87, hlam, hphi, ht23, p94_1, u2ehi4, u3elo1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h82, hc01, hc15, hlam, hphi, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h86, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h88, hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h89, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                          · linarith only [h93, hlam, hphi, ht23, u2ehi2, u3elo4]
                        · linarith only [h92, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h0, h84, h91, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h84, h90, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h127 | h127
                          · rcases h0bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h40, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h82, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, h88, hc12, hlam, hphi, ht01, ht0b, ht5b, p128_1, u5ehi0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, h85, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi3]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p128_1, u5ehi0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h40, hc01, hlam, hphi, ht12, ht23, p128_1, u3elo1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h84, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h40, h85, hlam, hphi, ht23, p128_1, u2ehi3, u3elo1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h40, h86, hlam, hphi, ht23, p128_1, u2ehi4, u3elo1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h89, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h85, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h87, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h89, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h82, hc01, hc15, hlam, hphi, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h86, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h88, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h40, h88, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p128_1, u3elo1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                          · linarith only [h127, hlam, hphi, ht23, u2ehi2, u3elo4]
                        · linarith only [h126, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h0, h125, h84, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h124, h84, hlam]
                · linarith only [h84, h88, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h84, h87, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h84, h86, hc25, hlam, hphi, u2ehi2]
          · linarith only [h84, h85, hc24, hlam, hphi, u2ehi2]
        · linarith only [h84, hlam, hphi, ht23, u2ehi0, u3elo2]

end R2N4
