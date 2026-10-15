import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases h0bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p13_1, u3ehi0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi3]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h10, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h11, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p13_1, u3ehi3]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi3]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h10, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, hlam, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h10, h2, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h10, h2, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h1, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h4, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h6, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h10, h2, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h5, hlam, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h7, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h8, hlam, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                          · linarith only [h11, h12, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                          · linarith only [h0, h11, h40, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h40, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                      · linarith only [h10, h9, hc25, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h44, h9, hc24, hlam, hphi, u2ehi4]
                      · linarith only [h44, h5, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
                  · linarith only [h4, h8, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h7, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h49 | h49
                · linarith only [h49, h6, hc34, hlam, hphi, u3ehi4]
                · linarith only [h49, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · linarith only [h5, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h54 | h54
          · linarith only [h3, h54, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h56 | h56
            · linarith only [h3, h56, hc23, hlam, hphi, u2ehi4]
            · linarith only [h56, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h2, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h60 | h60
      · rcases m.htr 0 2 3 (by decide) (by decide) with h61 | h61
        · rcases m.htr 0 2 4 (by decide) (by decide) with h62 | h62
          · linarith only [h0, h1, h62, hlam]
          · linarith only [h61, h62, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h65 | h65
          · linarith only [h61, h65, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h67 | h67
            · linarith only [h61, h67, hc23, hlam, hphi, u2ehi4]
            · linarith only [h67, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h60, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h71 | h71
    · rcases m.htr 0 1 5 (by decide) (by decide) with h72 | h72
      · rcases m.htr 0 2 3 (by decide) (by decide) with h73 | h73
        · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
          · rcases m.htr 0 2 5 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                          · rcases h0bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h73, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p83_1, u3ehi3]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h72, h78, h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h72, h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h73, h81, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p83_1, u3ehi3]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h72, h78, h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h72, h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h71, h79, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi3]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h73, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h72, h73, h78, h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h72, h73, h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h71, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h74, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h76, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h72, h80, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h72, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h75, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h77, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h78, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                          · linarith only [h81, h82, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                          · linarith only [h0, h110, h71, h79, h81, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h110, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                      · linarith only [h0, h71, h79, h80, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h71, h75, h78, h79, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h74, h78, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h76, h77, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h117 | h117
                · linarith only [h117, h76, hc34, hlam, hphi, u3ehi4]
                · linarith only [h117, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · linarith only [h73, h75, hc25, hlam, hphi, u2ehi2]
          · linarith only [h73, h74, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h122 | h122
          · linarith only [h122, h73, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h122, h71, hlam]
      · linarith only [h71, h72, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
      · rcases m.htr 0 2 3 (by decide) (by decide) with h127 | h127
        · rcases m.htr 0 2 4 (by decide) (by decide) with h128 | h128
          · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
            · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
              · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                          · rcases h0bigk with h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, hlam, p137_1]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h130, h71, hlam, p137_1]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h71, hlam, p137_1]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h126, h134, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p137_1]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p137_1, u3ehi0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, h126, h134, h71, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, h126, h134, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h126, h134, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h127, hlam, p137_1]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, h126, h127, h134, h71, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, h126, h127, h134, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h126, h134, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h128, hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h130, hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h0, h126, h127, h130, h134, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p137_1, u2ehi4]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h126, hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h129, hlam, p137_1]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h131, hlam, p137_0]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [h132, hlam, p137_1]
                            · have p137_0 := h137c.1
                              have p137_1 := h137c.2.1
                              have p137_2 := h137c.2.2.1
                              have p137_3 := h137c.2.2.2
                              linarith only [hlam, p137_0]
                          · linarith only [h136, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                          · linarith only [h135, h164, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h164, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                      · linarith only [h0, h134, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                    · linarith only [h0, h126, h128, h133, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h126, h129, h132, h71, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                · linarith only [h130, h131, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h171 | h171
                · linarith only [h130, h171, hc34, hlam, hphi, u3ehi4]
                · linarith only [h171, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · linarith only [h129, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
          · linarith only [h127, h128, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h176 | h176
          · linarith only [h127, h176, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h178 | h178
            · linarith only [h127, h178, hc23, hlam, hphi, u2ehi4]
            · linarith only [h178, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h181 | h181
        · rcases m.htr 0 2 4 (by decide) (by decide) with h182 | h182
          · rcases m.htr 0 2 5 (by decide) (by decide) with h183 | h183
            · rcases m.htr 0 3 4 (by decide) (by decide) with h184 | h184
              · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
                · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h187 | h187
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h188 | h188
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h189 | h189
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                          · rcases h0bigk with h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [hlam, p191_0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, hlam, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h181, h189, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p191_1, u3ehi3]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h71, hlam, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h126, hlam, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [hlam, p191_0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, h181, h189, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p191_1, u3ehi3]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, h183, h186, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi4]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, h183, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi4]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, h181, hc01, hc12, hlam, hphi, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h181, hlam, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [hlam, p191_0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, h181, h183, h186, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi4]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, h181, h183, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi4]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h71, hc01, hc14, hlam, hphi, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h182, hlam, p191_0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h184, hlam, p191_0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [hlam, p191_0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h0, h181, h183, h184, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p191_1, u2ehi4]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p191_1, u5elo0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h183, hlam, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h185, hlam, p191_0]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [h186, hlam, p191_1]
                            · have p191_0 := h191c.1
                              have p191_1 := h191c.2.1
                              have p191_2 := h191c.2.2.1
                              have p191_3 := h191c.2.2.2
                              linarith only [hlam, p191_0]
                          · linarith only [h126, h185, h189, h190, hlam, hphi, ht34, ht45, u3ehi3, u5elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                          · linarith only [h0, h181, h184, h189, h218, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h218, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h0, h188, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                    · linarith only [h0, h182, h187, hlam]
                  · linarith only [h182, h186, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h184, h185, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h225 | h225
                · linarith only [h184, h225, hc34, hlam, hphi, u3ehi4]
                · linarith only [h225, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · linarith only [h183, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
          · linarith only [h181, h182, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h230 | h230
          · linarith only [h181, h230, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
            · linarith only [h181, h232, hc23, hlam, hphi, u2ehi4]
            · linarith only [h232, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_20_12_13_15_M_LI_L_R_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h14, h16, h9, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h0, h11, h13, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h0, h11, h13, h15, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h14, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h10, h13, h6, h8, hlam, hphi, ht23, u2ehi4, u3elo0]
                          · linarith only [h12, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h11, h9, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h10, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                    · linarith only [h9, hlam, hphi, ht23, u2ehi1, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h1, h30, h8, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                                · linarith only [h33, h4, h8, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                                  · linarith only [h35, h4, h8, hlam, hphi, ht23, u2ehi3, u3elo3]
                                  · rcases h0bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo0, u2ehi0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h0, h26, h32, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1, u0elo0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo0, u2ehi3]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h2, h27, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo0, u2ehi4]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h0, h27, h29, h33, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo1, u2ehi3]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h0, h27, h29, h33, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo1, u2ehi3]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo1, u2ehi3]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h2, h27, h33, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo1, u2ehi3]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h0, hlam, p37_1]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h3, hlam, p37_1]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo2, u2ehi3]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h2, h27, h33, hlam, hphi, ht23, p37_1, u2ehi3, u3elo0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h1, hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h4, hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h6, hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h8, hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h2, hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h5, hlam, p37_1]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h7, hlam, p37_0]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p37_1, u0elo4, u2ehi3]
                                    · have p37_0 := h37c.1
                                      have p37_1 := h37c.2.1
                                      have p37_2 := h37c.2.2.1
                                      have p37_3 := h37c.2.2.2
                                      linarith only [hlam, p37_0]
                              · linarith only [h32, hlam, hphi, ht23, u2ehi2, u3elo3]
                          · linarith only [h29, h7, hc13, hlam, hphi, u3elo0]
                        · linarith only [h26, h28, hlam, hphi, ht23, u2ehi2, u3elo3]
                      · linarith only [h26, h27, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h26, hlam, hphi, ht23, u2ehi1, u3elo2]
                · linarith only [h3, h7, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h3, h6, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · linarith only [h3, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h73 | h73
        · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
          · rcases m.htr 0 2 5 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · linarith only [h0, h2, h77, hlam]
                · linarith only [h74, h76, h77, hlam, hphi, ht23, u2ehi3, u3elo4]
              · linarith only [h73, h76, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h73, h75, hc25, hlam, hphi, u2ehi2]
          · linarith only [h73, h74, hc24, hlam, hphi, u2ehi2]
        · linarith only [h73, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h84 | h84
      · rcases m.htr 0 2 3 (by decide) (by decide) with h85 | h85
        · rcases m.htr 0 2 4 (by decide) (by decide) with h86 | h86
          · rcases m.htr 0 2 5 (by decide) (by decide) with h87 | h87
            · rcases m.htr 0 3 4 (by decide) (by decide) with h88 | h88
              · linarith only [h0, h1, h88, hlam]
              · linarith only [h85, h88, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h85, h87, hc25, hlam, hphi, u2ehi2]
          · linarith only [h85, h86, hc24, hlam, hphi, u2ehi2]
        · linarith only [h85, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h94 | h94
        · rcases m.htr 0 2 4 (by decide) (by decide) with h95 | h95
          · rcases m.htr 0 2 5 (by decide) (by decide) with h96 | h96
            · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
              · linarith only [h0, h1, h97, hlam]
              · linarith only [h94, h97, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h94, h96, hc25, hlam, hphi, u2ehi2]
          · linarith only [h94, h95, hc24, hlam, hphi, u2ehi2]
        · linarith only [h94, hlam, hphi, ht23, u2ehi0, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h103 | h103
    · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
      · rcases m.htr 0 2 3 (by decide) (by decide) with h105 | h105
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · linarith only [h0, h103, h106, hlam, hphi, ht23, u2ehi3, u3elo1]
          · linarith only [h105, h106, hc24, hlam, hphi, u2ehi2]
        · linarith only [h105, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h110 | h110
        · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
          · linarith only [h0, h103, h111, hlam, hphi, ht23, u2ehi3, u3elo1]
          · linarith only [h110, h111, hc24, hlam, hphi, u2ehi2]
        · linarith only [h110, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
      · rcases m.htr 0 2 3 (by decide) (by decide) with h116 | h116
        · rcases m.htr 0 2 4 (by decide) (by decide) with h117 | h117
          · rcases m.htr 0 2 5 (by decide) (by decide) with h118 | h118
            · linarith only [h0, h115, h118, hlam, hphi, ht23, u2ehi4, u3elo1]
            · linarith only [h116, h118, hc25, hlam, hphi, u2ehi2]
          · linarith only [h116, h117, hc24, hlam, hphi, u2ehi2]
        · linarith only [h116, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h123 | h123
        · rcases m.htr 0 2 4 (by decide) (by decide) with h124 | h124
          · rcases m.htr 0 2 5 (by decide) (by decide) with h125 | h125
            · rcases m.htr 0 3 4 (by decide) (by decide) with h126 | h126
              · rcases m.htr 0 3 5 (by decide) (by decide) with h127 | h127
                · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h135 | h135
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                                  · linarith only [h123, h134, h136, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h123, h134, h135, h136, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h103, h128, h131, h135, hlam, hphi, ht23, u2ehi3, u3elo1]
                              · linarith only [h134, hlam, hphi, ht23, u2ehi2, u3elo3]
                            · linarith only [h103, h128, h133, hlam]
                          · linarith only [h0, h127, h132, hlam]
                        · linarith only [h0, h126, h131, hlam]
                      · linarith only [h125, h129, h130, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi2]
                    · linarith only [h129, hlam, hphi, ht23, u2ehi1, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                            · linarith only [h103, h128, h148, h150, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h153 | h153
                                · linarith only [h103, h124, h150, h153, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                                  · linarith only [h123, h152, h155, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · rcases h0bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p157_1, u0elo0, u2ehi0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h0, hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h103, hlam, p157_1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h115, hlam, p157_1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      rcases p157_3 (m.d 0 1) (by simp) with h163 | h163
                                      · linarith only [h163, hlam, p157_0]
                                      · rcases p157_3 (m.d 0 2) (by simp) with h165 | h165
                                        · rcases p157_3 (m.d 0 3) (by simp) with h166 | h166
                                          · linarith only [h123, h166, hlam]
                                          · linarith only [h0, h166, hlam]
                                        · linarith only [h165, hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h127, hc35, hlam, hphi, ht0b, ht5b, p157_1, u0elo1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h124, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p157_1, u0elo1, u2ehi3]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h125, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p157_1, u0elo1, u2ehi4]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, p157_1, u3elo0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h123, hlam, p157_1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h0, h124, hlam, hphi, ht23, p157_1, u2ehi3, u3elo1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h0, h125, hlam, hphi, ht23, p157_1, u2ehi4, u3elo1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h103, h150, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p157_1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h124, hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h126, hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h128, hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h115, h149, hc01, hlam, hphi, ht12, ht23, p157_1, u3elo1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h125, hlam, p157_1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h127, hlam, p157_0]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [h103, h115, h149, hc01, hlam, hphi, ht12, ht23, p157_1, u3elo1]
                                    · have p157_0 := h157c.1
                                      have p157_1 := h157c.2.1
                                      have p157_2 := h157c.2.2.1
                                      have p157_3 := h157c.2.2.2
                                      linarith only [hlam, p157_0]
                              · linarith only [h152, hlam, hphi, ht23, u2ehi2, u3elo3]
                          · linarith only [h0, h149, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h148, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h125, h147, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                    · linarith only [h146, hlam, hphi, ht23, u2ehi1, u3elo2]
                · linarith only [h123, h127, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h123, h126, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h123, h125, hc25, hlam, hphi, u2ehi2]
          · linarith only [h123, h124, hc24, hlam, hphi, u2ehi2]
        · linarith only [h123, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_15_M_LI_L_R_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · linarith only [h0, h2, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
        · linarith only [h2, h3, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12 | h12
        · linarith only [h12, h2, hc23, hlam, hphi, u2ehi4]
        · linarith only [h12, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h15 | h15
      · linarith only [h0, h1, h15, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h17 | h17
        · linarith only [h15, h17, hc23, hlam, hphi, u2ehi4]
        · linarith only [h17, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
    · rcases m.htr 0 2 3 (by decide) (by decide) with h21 | h21
      · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
            · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                        · linarith only [h20, h24, h27, h30, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h20, h25, h26, h29, h30, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h29, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h28, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h0, h20, h23, h27, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                · linarith only [h0, h20, h23, h24, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h0, h20, h24, h25, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h21, h24, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                · linarith only [h20, h23, h41, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h20, h39, h40, h41, h43, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                        · rcases h3bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h23, hc13, hc34, hlam, hphi, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h23, hc34, hlam, hphi, ht23, p48_1, u2ehi2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h23, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            rcases p48_3 (m.d 0 3) (by simp) with h53 | h53
                            · rcases p48_3 (m.d 1 3) (by simp) with h54 | h54
                              · linarith only [h20, h54, hlam]
                              · linarith only [h39, h45, h54, hlam]
                            · linarith only [h53, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h20, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h0, h20, h45, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi4]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h41, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h0, h20, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h21, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h39, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h43, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h21, hc35, hlam, hphi, ht0b, ht5b, p48_1, u0elo1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h21, hc34, hlam, hphi, ht23, p48_1, u2ehi2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h39, hc34, hlam, hphi, ht23, p48_1, u2ehi2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p48_1, u2ehi2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            rcases p48_3 (m.d 0 3) (by simp) with h72 | h72
                            · linarith only [h23, h72, hlam]
                            · linarith only [h20, h39, h45, h72, hlam]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h20, h39, h45, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h39, h45, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h45, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h47, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                        · linarith only [h20, h23, h39, h45, h47, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                      · linarith only [h43, h45, h46, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                    · linarith only [h45, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
              · linarith only [h0, h20, h39, h40, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h20, h21, h39, hlam]
        · linarith only [h22, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h20, h21, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h87 | h87
      · rcases m.htr 0 2 5 (by decide) (by decide) with h88 | h88
        · rcases m.htr 0 3 4 (by decide) (by decide) with h89 | h89
          · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
            · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
              · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                        · linarith only [h87, h93, h96, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h87, h93, h95, h96, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h95, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h94, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h89, h93, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                · linarith only [h20, h89, h92, hlam]
              · linarith only [h0, h87, h91, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h87, h90, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
            · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
              · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                  · linarith only [h108, h87, h89, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                        · rcases h3bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h20, hlam, p113_1]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h105, h107, h110, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p113_1, u2ehi4]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h89, hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h105, h107, h89, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p113_1]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            rcases p113_3 (m.d 0 3) (by simp) with h119 | h119
                            · linarith only [h119, h20, hlam]
                            · rcases p113_3 (m.d 1 3) (by simp) with h121 | h121
                              · rcases p113_3 (m.d 2 3) (by simp) with h122 | h122
                                · linarith only [h105, h122, hlam]
                                · rcases p113_3 (m.d 3 4) (by simp) with h124 | h124
                                  · linarith only [h107, h124, hlam]
                                  · linarith only [h124, h89, hlam]
                              · linarith only [h121, h20, hlam]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            rcases p113_3 (m.d 0 3) (by simp) with h129 | h129
                            · linarith only [h129, h20, hlam]
                            · linarith only [h129, h87, hlam]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h105, h20, h89, hc01, hc12, hlam, hphi, p113_1]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h107, h110, h87, h89, hlam, p113_2]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h87, hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h105, hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h108, hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h87, hc35, hlam, hphi, ht0b, ht5b, p113_1, u0elo1]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h87, hc34, hlam, hphi, ht23, p113_1, u2ehi2]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h107, hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h105, h107, h110, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p113_1, u2ehi4]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            rcases p113_3 (m.d 0 3) (by simp) with h143 | h143
                            · linarith only [h143, h89, hlam]
                            · linarith only [h110, h143, h87, hlam]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h110, h87, hlam, p113_1]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h107, h110, h87, h89, hlam, p113_1]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h110, hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [h112, hlam, p113_0]
                          · have p113_0 := h113c.1
                            have p113_1 := h113c.2.1
                            have p113_2 := h113c.2.2.1
                            have p113_3 := h113c.2.2.2
                            linarith only [hlam, p113_0]
                        · linarith only [h112, h87, h89, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h111, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h110, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                  · linarith only [h107, h154, h20, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                        · rcases h3bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h20, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h156, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p159_1, u0elo2, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h89, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h164 | h164
                            · rcases p159_3 (m.d 1 3) (by simp) with h165 | h165
                              · rcases p159_3 (m.d 2 3) (by simp) with h166 | h166
                                · linarith only [h166, h87, hlam]
                                · linarith only [h156, h166, hlam]
                              · linarith only [h165, h20, hlam, p159_1]
                            · linarith only [h164, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h107, hc03, hc34, hlam, hphi, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h107, h156, hc34, hlam, hphi, ht23, p159_1, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h107, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h175 | h175
                            · linarith only [h175, h20, hlam]
                            · linarith only [h156, h175, h87, hlam]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h87, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h105, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h154, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h158, h87, hc45, hlam, hphi, ht0b, ht5b, p159_1, u0elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h87, hc34, hlam, hphi, ht23, p159_1, u2ehi2]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h20, h87, hc34, hlam, hphi, ht23, p159_1, u2ehi2]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p159_1, u2ehi2]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 3) (by simp) with h187 | h187
                            · linarith only [h187, h89, hlam]
                            · linarith only [h156, h187, h87, hlam]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h156, h87, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h156, h20, h87, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h156, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h158, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                        · linarith only [h156, h158, h87, h89, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                      · linarith only [h157, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h156, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
              · linarith only [h0, h106, h87, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h105, h87, h88, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi4]
        · linarith only [h87, h88, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h201 | h201
        · linarith only [h201, h87, hc23, hlam, hphi, u2ehi4]
        · linarith only [h201, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_20_12_13_15_M_LR_L_R_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h0, h4, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h12, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h11, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
            · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h18, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h1, h18, h20, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h1, h18, h22, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi4]
                    · linarith only [h22, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
              · linarith only [h17, h4, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
              · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                · linarith only [h27, h4, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                  · linarith only [h1, h27, h29, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h1, h27, h31, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi4]
                    · linarith only [h31, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
              · linarith only [h26, h4, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo3]
        · linarith only [h1, h3, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
        · rcases m.htr 0 2 3 (by decide) (by decide) with h37 | h37
          · rcases m.htr 0 3 4 (by decide) (by decide) with h38 | h38
            · linarith only [h1, h2, h38, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                · linarith only [h0, h2, h41, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h37, h41, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h40, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h45 | h45
            · linarith only [h1, h2, h45, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h47 | h47
              · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                · linarith only [h0, h2, h37, h48, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                  · linarith only [h0, h2, h50, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h1, h2, h48, h50, hc24, hlam, hphi, u2ehi1]
              · linarith only [h47, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h1, h36, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h55 | h55
      · rcases m.htr 0 1 5 (by decide) (by decide) with h56 | h56
        · rcases m.htr 0 2 3 (by decide) (by decide) with h57 | h57
          · linarith only [h0, h1, h57, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h59 | h59
            · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
              · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                · linarith only [h57, h61, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h1, h61, hc23, hlam, hphi, u2ehi1]
              · linarith only [h59, h60, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h0, h1, h59, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h0, h56, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h67 | h67
        · rcases m.htr 0 2 3 (by decide) (by decide) with h68 | h68
          · linarith only [h0, h1, h68, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h70 | h70
            · rcases m.htr 0 3 5 (by decide) (by decide) with h71 | h71
              · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                · linarith only [h0, h68, h72, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                · linarith only [h0, h1, h72, hc23, hlam, hphi, u2ehi1]
              · linarith only [h70, h71, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h0, h1, h70, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h0, h67, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h78 | h78
    · rcases m.htr 0 1 4 (by decide) (by decide) with h79 | h79
      · rcases m.htr 0 1 5 (by decide) (by decide) with h80 | h80
        · rcases m.htr 0 2 3 (by decide) (by decide) with h81 | h81
          · rcases m.htr 0 3 4 (by decide) (by decide) with h82 | h82
            · rcases m.htr 0 3 5 (by decide) (by decide) with h83 | h83
              · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                                · linarith only [h78, h84, h89, h92, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h0, h78, h85, h87, h91, h92, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h91, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                            · linarith only [h90, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                          · linarith only [h0, h78, h82, h89, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h87, h88, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h78, h82, h84, h87, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h0, h86, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h78, h84, h85, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h84, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h82, h83, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
              · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                      · linarith only [h108, h78, h82, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                          · linarith only [h104, h111, h82, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                                · rcases h3bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h107, h110, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p116_1, u0elo2, u2ehi4]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h82, hc23, hc34, hlam, hphi, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h82, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    rcases p116_3 (m.d 0 3) (by simp) with h121 | h121
                                    · rcases p116_3 (m.d 1 3) (by simp) with h122 | h122
                                      · linarith only [h122, h78, hlam]
                                      · linarith only [h110, h122, hlam]
                                    · linarith only [h121, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h78, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h0, h108, h113, h79, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p116_1, u2ehi4]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h108, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h0, h108, h115, h79, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h81, hlam, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h105, hlam, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h111, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h115, h81, hc45, hlam, hphi, ht0b, ht5b, p116_1, u0elo1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p116_1, u0ehi7]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h105, hc34, hlam, hphi, ht23, p116_1, u2ehi2]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht23, p116_1, u2ehi2]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    rcases p116_3 (m.d 0 3) (by simp) with h140 | h140
                                    · linarith only [h140, h82, hlam]
                                    · linarith only [h104, h140, hlam]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h104, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h110, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h113, hlam, p116_0]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [h115, hlam, p116_1]
                                  · have p116_0 := h116c.1
                                    have p116_1 := h116c.2.1
                                    have p116_2 := h116c.2.2.1
                                    have p116_3 := h116c.2.2.2
                                    linarith only [hlam, p116_0]
                                · linarith only [h0, h104, h107, h108, h110, h115, h79, h82, hc12, hlam, hphi, ht01, ht23, ht34, ht45, u0ehi9, u2ehi4, u5elo4]
                              · linarith only [h111, h113, h114, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                            · linarith only [h113, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                        · linarith only [h104, h110, h82, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h107, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h105, h106, h78, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h105, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h104, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
          · linarith only [h0, h78, h81, hlam]
        · linarith only [h79, h80, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 2 3 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 3 4 (by decide) (by decide) with h160 | h160
            · linarith only [h160, h78, h79, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
              · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                · rcases m.htr 1 2 4 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                      · linarith only [h160, h162, h164, h166, h78, h79, hc12, hlam, hphi, ht01, u0ehi9]
                      · linarith only [h163, h166, h78, h79, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h163, h164, h165, h78, h79, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h163, h164, h78, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h163, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h162, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
          · linarith only [h0, h159, h78, hlam]
        · linarith only [h158, h78, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h175 | h175
      · rcases m.htr 0 1 5 (by decide) (by decide) with h176 | h176
        · rcases m.htr 0 2 3 (by decide) (by decide) with h177 | h177
          · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
            · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
                · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                                · linarith only [h177, h185, h188, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h175, h177, h181, h187, h188, h78, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h187, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                            · linarith only [h186, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                          · linarith only [h177, h178, h185, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h184, h78, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h175, h181, h183, h78, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h175, h180, h181, h182, h78, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h180, h181, h78, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h177, h180, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h175, h179, h78, hc14, hlam, hphi, ht45, u5elo3]
            · linarith only [h175, h178, h78, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h201 | h201
            · rcases m.htr 0 3 5 (by decide) (by decide) with h202 | h202
              · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
                · linarith only [h0, h175, h177, h203, hc12, hlam, hphi, ht01, u0ehi8]
                · linarith only [h0, h175, h203, hc23, hlam, hphi, ht01, ht12, u0ehi8]
              · linarith only [h0, h175, h177, h202, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo3]
            · linarith only [h0, h175, h177, h201, hlam]
        · linarith only [h175, h176, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h209 | h209
        · rcases m.htr 0 2 3 (by decide) (by decide) with h210 | h210
          · rcases m.htr 0 3 4 (by decide) (by decide) with h211 | h211
            · rcases m.htr 0 3 5 (by decide) (by decide) with h212 | h212
              · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h219 | h219
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h220 | h220
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h221 | h221
                                · linarith only [h210, h218, h221, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h210, h218, h220, h221, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h220, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                            · linarith only [h219, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                          · linarith only [h210, h211, h218, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h175, h216, h217, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h209, h210, h211, h215, h216, h78, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi4]
                    · linarith only [h209, h213, h215, h78, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h209, h213, h214, h78, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h209, h213, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h211, h212, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h236 | h236
                    · linarith only [h209, h211, h236, h78, hc34, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h234, h236, h78, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h209, h234, h235, h78, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h210, h234, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h209, h233, h78, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h242 | h242
            · rcases m.htr 0 3 5 (by decide) (by decide) with h243 | h243
              · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
                · linarith only [h210, h244, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h209, h244, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h0, h209, h210, h243, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h248 | h248
              · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
                · linarith only [h0, h209, h210, h249, hc12, hlam, hphi, ht01, u0ehi9]
                · linarith only [h0, h209, h249, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h0, h209, h210, h248, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo3]
        · linarith only [h209, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo1]

end R2N4
