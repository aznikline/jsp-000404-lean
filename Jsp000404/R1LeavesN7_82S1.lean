import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_R_L_R_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h5, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h5, h6, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h2, h4, h5, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h3bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 3) (by simp) with h15 | h15
                        · rcases p13_3 (m.d 1 3) (by simp) with h16 | h16
                          · linarith only [h1, h16, hlam]
                          · rcases p13_3 (m.d 2 3) (by simp) with h18 | h18
                            · linarith only [h18, h2, hlam]
                            · rcases p13_3 (m.d 3 4) (by simp) with h20 | h20
                              · linarith only [h20, h3, hlam]
                              · rcases p13_3 (m.d 3 5) (by simp) with h22 | h22
                                · linarith only [h22, h4, hlam]
                                · linarith only [h22, h6, hlam]
                        · linarith only [h1, h15, hlam]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 3) (by simp) with h26 | h26
                        · rcases p13_3 (m.d 1 3) (by simp) with h27 | h27
                          · linarith only [h1, h27, hlam]
                          · linarith only [h27, h5, hlam]
                        · linarith only [h2, h26, hlam]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h4, h5, h6, h8, hlam, p13_2]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h2, h5, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi3]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h1, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h6, h8, hc35, hlam, hphi, ht23, p13_1, u2ehi3]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h2, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h6, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h2, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h5, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h9, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h3, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h5, hc34, hlam, hphi, ht23, p13_1, u2ehi2]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h8, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h11, hlam, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h4, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h5, hc35, hlam, hphi, ht23, p13_1, u2ehi2]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h2, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi3]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 3) (by simp) with h51 | h51
                        · rcases p13_3 (m.d 1 3) (by simp) with h52 | h52
                          · linarith only [h52, h6, hlam]
                          · linarith only [h5, h52, h8, hlam]
                        · linarith only [h3, h51, hlam]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h57, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h0, h2, h3, h59, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h59, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
              · linarith only [h1, h62, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h0, h2, h65, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h2, h4, h5, h65, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h5, h64, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
            · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
              · linarith only [h4, h70, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                  · linarith only [h0, h3, h4, h69, h73, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                    · linarith only [h0, h69, h72, h75, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h3bigk with h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h4, h75, hc13, hc45, hlam, hphi, ht34, p77_1]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h4, h75, hc23, hc45, hlam, hphi, ht34, p77_1]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h4, h75, hc34, hc45, hlam, hphi, p77_1]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h4, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h1, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h1, h3, h4, h72, h75, hc01, hc45, hlam, hphi, ht23, ht34, p77_1, u0ehi3, u2ehi3]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h1, h4, h75, hc34, hc45, hlam, hphi, p77_1]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h70, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h2, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h69, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h2, h4, h75, hc34, hc45, hlam, hphi, p77_1]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h73, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h3, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h3, h4, h75, hc13, hc45, hlam, hphi, ht34, p77_1]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h72, hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [hlam, p77_0]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h75, hlam, p77_1]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h3, h75, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p77_1, u0ehi3]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h69, h75, hc45, hlam, hphi, ht23, ht34, p77_1, u2ehi2]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [h72, h75, hc45, hlam, hphi, ht23, ht34, p77_1, u2ehi3]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        rcases p77_3 (m.d 0 3) (by simp) with h101 | h101
                        · linarith only [h101, h4, hlam]
                        · linarith only [h101, h3, hlam]
                      · have p77_0 := h77c.1
                        have p77_1 := h77c.2.1
                        have p77_2 := h77c.2.2.1
                        have p77_3 := h77c.2.2.2
                        linarith only [hlam, p77_0]
                · linarith only [h3, h4, h72, hc23, hc35, hlam, hphi]
            · linarith only [h2, h4, h69, hc35, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
          · linarith only [h107, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
            · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
              · linarith only [h107, h110, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                · linarith only [h109, h112, h3, hc12, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h1, h107, h109, h114, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                    · rcases h3bigk with h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h107, h109, hc23, hc35, hlam, hphi, p117_1]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h107, hc35, hlam, hphi, ht23, p117_1, u2ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h3, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h107, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h1, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h1, h107, h116, hlam, p117_1]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h110, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h2, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h109, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h112, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h114, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p117_1, u0ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h109, hc34, hlam, hphi, ht23, p117_1, u2ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hc34, hlam, hphi, ht23, p117_1, u2ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p117_1, u5ehi0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p117_1, u0ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h109, hc35, hlam, hphi, ht23, p117_1, u2ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p117_1, u2ehi2]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [h116, hlam, p117_0]
                      · have p117_0 := h117c.1
                        have p117_1 := h117c.2.1
                        have p117_2 := h117c.2.2.1
                        have p117_3 := h117c.2.2.2
                        linarith only [hlam, p117_0]
                    · linarith only [h116, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
            · linarith only [h109, h2, h3, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h145 | h145
        · rcases m.htr 0 3 5 (by decide) (by decide) with h146 | h146
          · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
            · linarith only [h147, h2, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
              · linarith only [h1, h149, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h146, h147, h149, h2, hc23, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
            · linarith only [h152, h2, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
              · linarith only [h146, h154, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                  · linarith only [h145, h146, h157, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h157, h2, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h145, h156, h2, hc03, hlam, hphi, u0ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
          · linarith only [h145, h161, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
            · linarith only [h0, h163, h2, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h165 | h165
              · linarith only [h1, h145, h161, h165, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                · linarith only [h145, h167, h2, hc23, hlam, hphi, u2ehi0]
                · linarith only [h167, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h170 | h170
      · linarith only [h0, h1, h170, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
        · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
          · rcases m.htr 1 2 3 (by decide) (by decide) with h174 | h174
            · linarith only [h0, h1, h170, h174, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
            · linarith only [h0, h1, h174, hc23, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h173, hc35, hlam, hphi, ht23, u2ehi1]
        · linarith only [h0, h1, h172, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h179 | h179
    · rcases m.htr 0 2 3 (by decide) (by decide) with h180 | h180
      · rcases m.htr 0 3 4 (by decide) (by decide) with h181 | h181
        · rcases m.htr 0 3 5 (by decide) (by decide) with h182 | h182
          · linarith only [h0, h179, h182, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
            · rcases m.htr 1 3 5 (by decide) (by decide) with h185 | h185
              · linarith only [h0, h179, h182, h185, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                  · linarith only [h0, h179, h181, h182, h184, h188, hc12, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h190 | h190
                    · linarith only [h181, h190, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h3bigk with h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h182, h184, h187, h190, hc45, hlam, hphi, ht23, ht34, p192_1, u2ehi3]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h182, h187, h190, hc45, hlam, hphi, ht23, ht34, p192_1, u2ehi3]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h182, h190, hc34, hc45, hlam, hphi, p192_1]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h182, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h179, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h0, h179, h187, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p192_1, u2ehi3]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h0, h179, h181, h182, h190, hc12, hc34, hc45, hlam, hphi, ht01, p192_1, u0ehi3]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h185, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h180, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h184, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h180, h182, h190, hc34, hc45, hlam, hphi, p192_1]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h188, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h181, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h184, hc34, hlam, hphi, ht23, p192_1, u2ehi2]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h187, hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [hlam, p192_0]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h190, hlam, p192_1]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h181, h190, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p192_1, u0ehi3]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h184, h190, hc45, hlam, hphi, ht23, ht34, p192_1, u2ehi2]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [h187, h190, hc45, hlam, hphi, ht23, ht34, p192_1, u2ehi3]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        rcases p192_3 (m.d 0 3) (by simp) with h216 | h216
                        · linarith only [h182, h216, hlam]
                        · linarith only [h181, h216, hlam]
                      · have p192_0 := h192c.1
                        have p192_1 := h192c.2.1
                        have p192_2 := h192c.2.2.1
                        have p192_3 := h192c.2.2.2
                        linarith only [hlam, p192_0]
                · linarith only [h0, h179, h181, h187, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h0, h184, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h222 | h222
          · linarith only [h0, h179, h222, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
            · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
              · linarith only [h0, h179, h222, h225, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                · linarith only [h0, h179, h181, h224, h227, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                  · linarith only [h0, h179, h222, h224, h229, hc12, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                    · rcases h3bigk with h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h222, h224, hc35, hlam, hphi, ht23, p232_1, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h222, hc35, hlam, hphi, ht23, p232_1, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h181, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h222, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h179, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h0, h179, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p232_1, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h0, h179, h222, h231, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p232_1]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h225, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h180, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h224, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h227, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h229, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p232_1, u0ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h224, hc34, hlam, hphi, ht23, p232_1, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hc34, hlam, hphi, ht23, p232_1, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h0, h179, h222, h224, hc12, hc34, hlam, hphi, ht01, ht23, p232_1, u0ehi2, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h0, h179, h224, hc12, hc35, hlam, hphi, ht01, ht23, p232_1, u0ehi2, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h224, hc35, hlam, hphi, ht23, p232_1, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p232_1, u2ehi2]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [h231, hlam, p232_0]
                      · have p232_0 := h232c.1
                        have p232_1 := h232c.2.1
                        have p232_2 := h232c.2.2.1
                        have p232_3 := h232c.2.2.2
                        linarith only [hlam, p232_0]
                    · linarith only [h0, h179, h181, h224, h231, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi2, u2ehi2]
            · linarith only [h0, h224, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h179, h180, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h261 | h261
      · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 3 5 (by decide) (by decide) with h263 | h263
          · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
            · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
              · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                · rcases m.htr 2 3 5 (by decide) (by decide) with h267 | h267
                  · linarith only [h261, h267, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h269 | h269
                    · linarith only [h262, h269, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h3bigk with h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h179, hlam, p271_1]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        rcases p271_3 (m.d 0 3) (by simp) with h274 | h274
                        · rcases p271_3 (m.d 1 3) (by simp) with h275 | h275
                          · rcases p271_3 (m.d 2 3) (by simp) with h276 | h276
                            · linarith only [h261, h276, hlam]
                            · rcases p271_3 (m.d 3 4) (by simp) with h278 | h278
                              · linarith only [h262, h278, hlam]
                              · rcases p271_3 (m.d 3 5) (by simp) with h280 | h280
                                · linarith only [h263, h280, hlam]
                                · linarith only [h267, h280, hlam]
                          · linarith only [h264, h275, hlam]
                        · linarith only [h261, h274, hlam]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h263, h266, h267, hlam, p271_2]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h266, h267, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi3]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h264, hc12, hlam, hphi, ht01, p271_1, u0ehi2]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        rcases p271_3 (m.d 0 3) (by simp) with h289 | h289
                        · linarith only [h179, h289, hlam]
                        · linarith only [h261, h289, hlam]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h179, h263, h266, h267, hlam, p271_2]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h266, h267, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi3]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h261, hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h264, hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h263, h267, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p271_1]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h267, hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h262, hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h179, h263, h266, h267, hc34, hlam, hphi, ht23, p271_1, u2ehi3]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h266, hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h269, hlam, p271_1]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h263, hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h265, hlam, p271_0]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [h0, h261, h263, h266, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi3]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        rcases p271_3 (m.d 0 3) (by simp) with h307 | h307
                        · rcases p271_3 (m.d 1 3) (by simp) with h308 | h308
                          · rcases p271_3 (m.d 2 3) (by simp) with h309 | h309
                            · linarith only [h267, h309, hlam]
                            · linarith only [h266, h309, hlam]
                          · linarith only [h179, h263, h266, h267, h308, hlam]
                        · linarith only [h262, h307, hlam]
                      · have p271_0 := h271c.1
                        have p271_1 := h271c.2.1
                        have p271_2 := h271c.2.2.1
                        have p271_3 := h271c.2.2.2
                        linarith only [hlam, p271_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h315 | h315
                  · linarith only [h262, h266, h315, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h317 | h317
                    · linarith only [h0, h261, h262, h317, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h266, h317, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h179, h265, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h261, h264, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
            · rcases m.htr 1 3 5 (by decide) (by decide) with h323 | h323
              · linarith only [h263, h322, h323, hc12, hlam, hphi, ht01, u0ehi2]
              · linarith only [h179, h323, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h261, h322, hc02, hlam, hphi, u0ehi0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h327 | h327
          · linarith only [h262, h327, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
            · rcases m.htr 1 3 5 (by decide) (by decide) with h330 | h330
              · linarith only [h327, h330, hc13, hlam, hphi, ht01, u0ehi2]
              · linarith only [h179, h330, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h261, h262, h329, hc34, hlam, hphi, ht23, u2ehi0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h334 | h334
        · rcases m.htr 0 3 5 (by decide) (by decide) with h335 | h335
          · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
            · linarith only [h0, h261, h336, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h336, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
            · linarith only [h0, h261, h339, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h339, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h342 | h342
          · linarith only [h334, h342, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
            · linarith only [h0, h261, h344, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h344, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem r1l7_10_12_23_L_0_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
          · linarith only [h1, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · linarith only [h2, h3, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
        · linarith only [h10, h2, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · linarith only [h0, h13, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h10, h15, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h12, h17, h2, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h10, h12, h19, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                      · rcases h3bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23_1, u0elo2, u2ehi2]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h10, h22, hc34, hlam, hphi, ht23, p23_1, u2ehi2]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h2, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h10, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23_1, u0elo0, u2ehi2]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h13, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h15, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h1, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h12, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h17, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h19, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hc34, hlam, hphi, p23_1, u3ehi0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hc34, hlam, hphi, p23_1, u3ehi1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hc34, hlam, hphi, ht23, p23_1, u2ehi2]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hc34, hlam, hphi, p23_1, u3ehi4]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h12, hc35, hlam, hphi, ht23, p23_1, u2ehi2]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h12, hc35, hlam, hphi, ht23, p23_1, u2ehi2]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hc35, hlam, hphi, ht23, p23_1, u2ehi2]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h22, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                      · linarith only [h17, h21, h22, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h21, h50, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h12, h2, h50, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h1, h12, h2, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h54 | h54
      · rcases m.htr 0 3 5 (by decide) (by decide) with h55 | h55
        · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
          · linarith only [h0, h1, h56, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
            · linarith only [h0, h58, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h54, h58, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · linarith only [h54, h55, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h62 | h62
        · linarith only [h54, h62, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
          · linarith only [h0, h1, h64, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
            · linarith only [h0, h54, h66, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
              · linarith only [h0, h62, h68, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                · linarith only [h0, h54, h64, h70, hc23, hlam, hphi, u2ehi1]
                · linarith only [h1, h70, hc34, hlam, hphi, ht23, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h73 | h73
    · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
      · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
        · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
          · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
            · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
              · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                · linarith only [h73, h79, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h74, h79, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
              · linarith only [h0, h75, h78, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h74, h75, h77, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
          · linarith only [h73, h76, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · linarith only [h74, h75, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h86 | h86
        · linarith only [h74, h86, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
          · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
            · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
              · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                · linarith only [h73, h74, h91, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                  · linarith only [h73, h86, h93, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                      · rcases h3bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, hlam, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h86, h88, h89, h96, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p97_1, u3ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h74, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h86, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h103 | h103
                          · linarith only [h0, h103, hlam]
                          · rcases p97_3 (m.d 1 3) (by simp) with h105 | h105
                            · rcases p97_3 (m.d 2 3) (by simp) with h106 | h106
                              · linarith only [h106, h88, hlam]
                              · rcases p97_3 (m.d 3 4) (by simp) with h108 | h108
                                · linarith only [h108, h89, hlam]
                                · linarith only [h108, h74, hlam]
                            · linarith only [h0, h105, hlam]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h113 | h113
                          · linarith only [h0, h113, hlam]
                          · linarith only [h113, h73, hlam]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h86, h88, h96, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p97_1, u3ehi0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h73, h86, h88, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p97_1, u2ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h73, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h88, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h91, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h93, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h73, hc34, hlam, hphi, ht23, p97_1, u2ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h89, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h88, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p97_1, u2ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h73, h86, h88, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p97_1, u2ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h73, hc35, hlam, hphi, ht23, p97_1, u2ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h90, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h88, h90, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p97_1, u2ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h96, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                      · linarith only [h73, h74, h95, h96, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                      · linarith only [h134, h91, h95, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h134, h73, h74, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h73, h74, h89, h90, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
              · linarith only [h138, h89, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                · linarith only [h140, h73, h74, h89, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                  · linarith only [h0, h138, h142, h73, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h145 | h145
                      · rcases h3bigk with h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, hlam, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p146_1, u0elo2, u2ehi2]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h74, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h86, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h138, h145, hc34, hlam, hphi, p146_1, u3ehi0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h138, h145, hc34, hlam, hphi, ht23, p146_1, u2ehi2]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h89, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h138, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h73, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h88, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h140, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h142, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h73, hc34, hlam, hphi, ht23, p146_1, u2ehi2]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hc34, hlam, hphi, ht23, p146_1, u2ehi2]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hc34, hlam, hphi, p146_1, u3ehi4]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h73, hc35, hlam, hphi, ht23, p146_1, u2ehi2]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, h73, hc35, hlam, hphi, ht23, p146_1, u2ehi2]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hc35, hlam, hphi, ht23, p146_1, u2ehi2]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h145, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                      · linarith only [h144, h145, h73, h74, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h140, h144, h173, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h173, h73, h74, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h73, h74, h88, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h177 | h177
      · rcases m.htr 0 3 5 (by decide) (by decide) with h178 | h178
        · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
          · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
            · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
              · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                      · rcases h3bigk with h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h0, hlam, p186_1]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h73, hlam, p186_1]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h179, h185, h73, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p186_1, u3ehi4]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h179, h73, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p186_1, u3ehi4]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h177, h185, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p186_1, u3ehi4]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h179, h73, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p186_1, u2ehi0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          rcases p186_3 (m.d 0 3) (by simp) with h195 | h195
                          · linarith only [h0, h195, hlam]
                          · linarith only [h177, h195, hlam]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          rcases p186_3 (m.d 0 3) (by simp) with h198 | h198
                          · linarith only [h0, h198, hlam]
                          · linarith only [h178, h198, hlam]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h177, h185, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u3ehi4]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h179, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h179, h185, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p186_1, u3ehi4]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h179, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p186_1, u3ehi4]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h177, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h180, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h182, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h177, hlam, hphi, ht0b, ht34, ht45, ht5b, p186_1, u0elo2, u3ehi4]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h178, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h181, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h183, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h185, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                      · linarith only [h179, h182, h184, h185, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h217 | h217
                      · linarith only [h184, h217, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h3bigk with h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h0, hlam, p219_1]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h73, hlam, p219_1]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h179, h73, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p219_1, u3ehi3]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h179, h73, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p219_1, u3ehi4]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h177, h179, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p219_1, u3ehi3]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h179, h73, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p219_1, u2ehi0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h228 | h228
                          · linarith only [h0, h228, hlam]
                          · linarith only [h177, h228, hlam]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h231 | h231
                          · linarith only [h0, h231, hlam]
                          · linarith only [h178, h231, hlam]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h178, h217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p219_1, u3ehi3]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h179, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h179, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p219_1, u3ehi3]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h179, h217, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p219_1, u3ehi3]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h177, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h180, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h182, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h217, hlam, p219_1]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h178, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h181, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h183, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h178, hlam, hphi, ht0b, ht34, ht45, ht5b, p219_1, u0elo2, u3ehi3]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                  · linarith only [h178, h183, h73, hlam]
                · linarith only [h178, h182, h73, hc34, hlam, hphi, u3ehi4]
              · linarith only [h178, h181, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
            · linarith only [h177, h179, h180, h73, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
            · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
              · rcases m.htr 2 3 4 (by decide) (by decide) with h255 | h255
                · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
                      · rcases h3bigk with h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h0, hlam, p259_1]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h73, hlam, p259_1]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h258, hc45, hlam, hphi, ht0b, ht5b, p259_1, u0elo2]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1, u0elo2, u3ehi4]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h179, h73, hc23, hlam, hphi, p259_1, u2ehi0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h179, hlam, p259_1]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          rcases p259_3 (m.d 0 3) (by simp) with h268 | h268
                          · linarith only [h0, h268, hlam]
                          · linarith only [h177, h268, hlam]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          rcases p259_3 (m.d 0 3) (by simp) with h271 | h271
                          · linarith only [h0, h271, hlam]
                          · linarith only [h178, h271, hlam]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h177, h258, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p259_1, u3ehi4]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p259_1]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          rcases p259_3 (m.d 0 3) (by simp) with h277 | h277
                          · linarith only [h277, h73, hlam]
                          · linarith only [h177, h277, hlam]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          rcases p259_3 (m.d 0 3) (by simp) with h280 | h280
                          · linarith only [h280, h73, hlam]
                          · linarith only [h178, h280, hlam]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h177, hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h253, hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h255, hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h177, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1, u0elo2, u3ehi4]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h178, hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h254, hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h256, hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [h258, hlam, p259_0]
                        · have p259_0 := h259c.1
                          have p259_1 := h259c.2.1
                          have p259_2 := h259c.2.2.1
                          have p259_3 := h259c.2.2.2
                          linarith only [hlam, p259_0]
                      · rcases h3bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h0, hlam, p293_1]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h73, hlam, p293_1]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p293_1, u0elo2, u3ehi3]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h258, hlam, hphi, ht0b, ht34, ht45, ht5b, p293_1, u0elo2, u3ehi3]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h177, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u3ehi3]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h179, hlam, p293_1]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h302 | h302
                          · linarith only [h0, h302, hlam]
                          · linarith only [h177, h302, hlam]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h305 | h305
                          · linarith only [h0, h305, hlam]
                          · linarith only [h178, h305, hlam]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h178, h258, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p293_1, u3ehi3]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p293_1]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h311 | h311
                          · linarith only [h311, h73, hlam]
                          · linarith only [h177, h311, hlam]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h314 | h314
                          · linarith only [h314, h73, hlam]
                          · linarith only [h178, h314, hlam]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h177, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h253, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h255, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h258, hlam, p293_1]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h178, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h254, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h256, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h178, hlam, hphi, ht0b, ht34, ht45, ht5b, p293_1, u0elo2, u3ehi3]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h327 | h327
                      · linarith only [h257, h327, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h3bigk with h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h0, hlam, p329_1]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h73, hlam, p329_1]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p329_1, u0elo2, u3ehi3]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p329_1, u0elo2, u3ehi4]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h177, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p329_1, u3ehi3]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h179, hlam, p329_1]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          rcases p329_3 (m.d 0 3) (by simp) with h338 | h338
                          · linarith only [h0, h338, hlam]
                          · linarith only [h177, h338, hlam]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          rcases p329_3 (m.d 0 3) (by simp) with h341 | h341
                          · linarith only [h0, h341, hlam]
                          · linarith only [h178, h341, hlam]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h178, h327, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p329_1, u3ehi3]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p329_1]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          rcases p329_3 (m.d 0 3) (by simp) with h347 | h347
                          · linarith only [h347, h73, hlam]
                          · linarith only [h177, h347, hlam]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          rcases p329_3 (m.d 0 3) (by simp) with h350 | h350
                          · linarith only [h350, h73, hlam]
                          · linarith only [h178, h350, hlam]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h177, hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h253, hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h255, hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h327, hlam, p329_1]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h178, hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h254, hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h256, hlam, p329_0]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [h178, hlam, hphi, ht0b, ht34, ht45, ht5b, p329_1, u0elo2, u3ehi3]
                        · have p329_0 := h329c.1
                          have p329_1 := h329c.2.1
                          have p329_2 := h329c.2.2.1
                          have p329_3 := h329c.2.2.2
                          linarith only [hlam, p329_0]
                  · linarith only [h178, h256, h73, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                · linarith only [h179, h255, hc34, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h178, h254, hlam]
            · linarith only [h0, h177, h253, hlam]
        · linarith only [h177, h178, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h368 | h368
        · linarith only [h177, h368, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
          · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
            · rcases m.htr 1 3 5 (by decide) (by decide) with h372 | h372
              · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                · linarith only [h177, h373, h73, hc23, hlam, hphi, u2ehi0]
                · linarith only [h370, h371, h373, h73, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h177, h371, h372, hc35, hlam, hphi, u3ehi0]
            · linarith only [h370, h371, h73, hc34, hlam, hphi, ht23, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h378 | h378
            · linarith only [h177, h370, h378, h73, hc23, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h380 | h380
              · linarith only [h378, h380, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h382 | h382
                · linarith only [h370, h378, h382, hc23, hlam, hphi, u2ehi1]
                · linarith only [h382, h73, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
