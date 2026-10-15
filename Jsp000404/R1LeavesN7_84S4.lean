import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_13_25_L_R_L_0_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · rcases h5bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hlam, hphi, ht23, p13_1, u2ehi4, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
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
                              linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p13_1, u2ehi4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, hlam, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h7, hlam, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h12, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h3, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h4, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h8, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h1, h10, h12, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h5, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h9, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h11, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h12, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                          · rcases h5bigk with h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hlam, hphi, ht23, p39_1, u2ehi4, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h12, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p39_1, u3elo0]
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
                              linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p39_1, u2ehi4]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h0, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h0, h12, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h2, hlam, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h7, hlam, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h12, h2, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h0, h12, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h4, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h8, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo4]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h12, hlam, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h5, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h9, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h11, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                        · linarith only [h11, h3, h5, hlam, hphi, ht23, u2ehi3, u3elo0]
                      · linarith only [h10, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h3, h5, h6, h9, hlam, hphi, ht23, u2ehi3, u3elo0]
                  · linarith only [h4, h8, hc13, hlam, hphi, u3elo0]
                · linarith only [h2, h3, h5, h7, hlam, hphi, ht23, u2ehi1, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                · linarith only [h6, h70, hc24, hlam, hphi, u2ehi4]
                · linarith only [h2, h3, h5, h70, hlam, hphi, ht23, u2ehi1, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
              · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h5, h76, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
                        · linarith only [h73, h76, h79, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                          · linarith only [h73, h76, h78, h81, hc23, hlam, hphi, u2ehi3]
                          · rcases h5bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h74, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p83_1, u3elo0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h5, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h0, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p83_1, u3elo0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h76, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h2, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h74, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h2, h81, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h79, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h4, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h75, hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p83_1, u3elo4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h81, hlam, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h2, hc45, hlam, hphi, ht23, ht34, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h74, hc45, hlam, hphi, ht23, ht34, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p83_1, u2ehi4]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [h81, hc34, hc45, hlam, hphi, p83_1]
                            · have p83_0 := h83c.1
                              have p83_1 := h83c.2.1
                              have p83_2 := h83c.2.2.1
                              have p83_3 := h83c.2.2.2
                              linarith only [hlam, p83_0]
                      · linarith only [h78, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h4, h75, hc13, hlam, hphi, u3elo0]
                · linarith only [h2, h4, h74, hlam, hphi, ht23, u2ehi1, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                · linarith only [h112, h73, hc24, hlam, hphi, u2ehi4]
                · linarith only [h112, h2, h4, hlam, hphi, ht23, u2ehi1, u3elo0]
          · linarith only [h1, h4, hlam, hphi, ht23, u2ehi2, u3elo4]
        · linarith only [h1, h3, hlam, hphi, ht23, u2ehi2, u3elo3]
      · linarith only [h1, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1, hlam, hphi, ht23, u2ehi0, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h119 | h119
    · rcases m.htr 0 2 5 (by decide) (by decide) with h120 | h120
      · rcases m.htr 0 3 4 (by decide) (by decide) with h121 | h121
        · rcases m.htr 0 3 5 (by decide) (by decide) with h122 | h122
          · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
            · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
              · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                          · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h0, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h121, h123, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h121, h123, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h121, h123, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h126, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h126, hlam, hphi, ht23, p131_1, u2ehi4, u3elo1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h126, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h126, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h120, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h125, hlam, p131_1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h0, h120, h126, h130, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h0, h120, h126, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo1]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h122, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h126, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo4]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h119, h128, h130, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p131_1, u3elo0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h123, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h127, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h129, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [h130, hlam, p131_0]
                            · have p131_0 := h131c.1
                              have p131_1 := h131c.2.1
                              have p131_2 := h131c.2.2.1
                              have p131_3 := h131c.2.2.2
                              linarith only [hlam, p131_0]
                          · rcases h5bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, hlam, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h126, hlam, hphi, ht23, p157_1, u2ehi4, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h126, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h126, h130, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h126, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h126, hlam, hphi, ht23, p157_1, u2ehi4, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h126, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h126, h130, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h120, hlam, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h125, hlam, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h120, h126, h130, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h120, h126, h130, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h122, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h126, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1, u3elo4]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h130, hlam, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h123, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h127, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h129, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h121, h123, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1, u3elo0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                        · linarith only [h121, h123, h129, hlam, hphi, ht23, u2ehi3, u3elo0]
                      · linarith only [h128, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h121, h123, h124, h127, hlam, hphi, ht23, u2ehi3, u3elo0]
                  · linarith only [h122, h126, hc13, hlam, hphi, u3elo0]
                · linarith only [h120, h122, h125, hlam, hphi, ht23, u2ehi1, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h188 | h188
                · linarith only [h124, h188, hc24, hlam, hphi, u2ehi4]
                · linarith only [h120, h121, h123, h188, hlam, hphi, ht23, u2ehi1, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
              · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                        · linarith only [h120, h123, h195, h196, hlam, hphi, ht23, u2ehi4, u3elo2]
                        · linarith only [h193, h194, h196, hlam, hphi, ht23, u2ehi3, u3elo1]
                      · linarith only [h195, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h201 | h201
                        · linarith only [h191, h194, h201, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                          · linarith only [h191, h194, h200, h203, hc23, hlam, hphi, u2ehi3]
                          · rcases h5bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [hlam, p205_0]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h0, hlam, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h201, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p205_1, u2ehi3]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h0, h193, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1, u3elo1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h123, hlam, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h193, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1, u3elo1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [hlam, p205_0]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h193, h201, hlam, hphi, ht23, p205_1, u2ehi3, u3elo1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h193, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1, u3elo1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h194, hlam, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h120, hlam, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h192, hlam, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [hlam, p205_0]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h192, h203, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h201, hlam, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h122, hlam, p205_0]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h193, hlam, p205_0]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1, u3elo4]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [hlam, p205_0]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h203, hlam, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p205_1, u2ehi4]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [h203, hc34, hc45, hlam, hphi, p205_1]
                            · have p205_0 := h205c.1
                              have p205_1 := h205c.2.1
                              have p205_2 := h205c.2.2.1
                              have p205_3 := h205c.2.2.2
                              linarith only [hlam, p205_0]
                      · linarith only [h200, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h122, h193, hc13, hlam, hphi, u3elo0]
                · linarith only [h120, h122, h192, hlam, hphi, ht23, u2ehi1, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                · linarith only [h191, h234, hc24, hlam, hphi, u2ehi4]
                · linarith only [h120, h122, h234, hlam, hphi, ht23, u2ehi1, u3elo0]
          · linarith only [h119, h122, hlam, hphi, ht23, u2ehi2, u3elo4]
        · linarith only [h119, h121, hlam, hphi, ht23, u2ehi2, u3elo3]
      · linarith only [h119, h120, hc25, hlam, hphi, u2ehi2]
    · linarith only [h119, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_12_13_25_L_R_L_I_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h11, h12, hc34, hlam, hphi, ht45, u5elo3]
                        · linarith only [h1, h11, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h6, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h5, h9, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h18, h2, h4, h8, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · linarith only [h18, h5, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h7, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
              · linarith only [h23, h5, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h2, h25, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h25, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                  · linarith only [h1, h31, h4, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                        · linarith only [h1, h33, h35, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                          · linarith only [h0, h29, h35, h37, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h1, h33, h37, h4, hc23, hc34, hlam, hphi]
                      · linarith only [h31, h33, h34, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h28, h33, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h3, h30, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
              · linarith only [h28, h29, hc24, hlam, hphi, u2ehi2]
            · linarith only [h2, h28, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h46 | h46
        · linarith only [h2, h46, hc23, hlam, hphi, u2ehi4]
        · linarith only [h46, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h49 | h49
      · linarith only [h0, h1, h49, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h51 | h51
        · linarith only [h49, h51, hc23, hlam, hphi, u2ehi4]
        · linarith only [h51, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h54 | h54
    · rcases m.htr 0 2 3 (by decide) (by decide) with h55 | h55
      · rcases m.htr 0 2 5 (by decide) (by decide) with h56 | h56
        · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
          · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
            · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
              · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                    · linarith only [h0, h54, h62, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h61, h62, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h0, h54, h57, h58, h61, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h54, h56, h57, h60, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h54, h58, h59, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h56, h58, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
            · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                  · linarith only [h54, h57, h72, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h0, h54, h74, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h69, h74, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h0, h54, h56, h69, h71, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo0]
              · linarith only [h0, h54, h69, h70, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h55, h69, hlam]
        · linarith only [h55, h56, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h54, h55, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h82 | h82
      · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
        · rcases m.htr 0 3 4 (by decide) (by decide) with h84 | h84
          · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
            · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                            · linarith only [h82, h91, h93, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h3bigk with h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h54, hlam, p95_1]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h54, h85, h92, hc12, hlam, hphi, ht01, ht0b, ht5b, p95_1, u5ehi8]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                rcases p95_3 (m.d 0 3) (by simp) with h99 | h99
                                · rcases p95_3 (m.d 1 3) (by simp) with h100 | h100
                                  · rcases p95_3 (m.d 2 3) (by simp) with h101 | h101
                                    · linarith only [h101, h82, hlam]
                                    · linarith only [h101, h91, hlam]
                                  · linarith only [h100, h88, hlam]
                                · linarith only [h99, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                rcases p95_3 (m.d 0 3) (by simp) with h106 | h106
                                · rcases p95_3 (m.d 1 3) (by simp) with h107 | h107
                                  · rcases p95_3 (m.d 2 3) (by simp) with h108 | h108
                                    · linarith only [h108, h82, hlam]
                                    · linarith only [h108, h92, hlam]
                                  · linarith only [h107, h89, hlam]
                                · linarith only [h106, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h82, h85, h92, hc12, hlam, hphi, ht01, ht0b, ht5b, p95_1, u5ehi8]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h85, h92, hc12, hlam, hphi, ht01, ht0b, ht5b, p95_1, u5ehi8]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                rcases p95_3 (m.d 0 3) (by simp) with h116 | h116
                                · linarith only [h116, h54, hlam]
                                · linarith only [h116, h84, hlam]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                rcases p95_3 (m.d 0 3) (by simp) with h119 | h119
                                · linarith only [h119, h54, hlam]
                                · linarith only [h119, h82, h92, hlam]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h82, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h85, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                rcases p95_3 (m.d 0 3) (by simp) with h125 | h125
                                · rcases p95_3 (m.d 1 3) (by simp) with h126 | h126
                                  · rcases p95_3 (m.d 2 3) (by simp) with h127 | h127
                                    · rcases p95_3 (m.d 3 4) (by simp) with h128 | h128
                                      · linarith only [h128, hlam, p95_0]
                                      · rcases p95_3 (m.d 3 5) (by simp) with h130 | h130
                                        · linarith only [h130, h92, hlam]
                                        · linarith only [h130, h93, hlam]
                                    · linarith only [h127, hlam, p95_0]
                                  · linarith only [h126, h88, hlam]
                                · linarith only [h125, h84, hlam]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h0, h82, hc12, hlam, hphi, ht01, ht0b, ht5b, p95_1, u5ehi8]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h84, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h88, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h91, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h93, hlam, p95_1]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h82, hc35, hlam, hphi, ht23, p95_1, u2ehi2]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h89, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [h92, hlam, p95_0]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [hc34, hlam, hphi, ht45, p95_1, u5elo3]
                              · have p95_0 := h95c.1
                                have p95_1 := h95c.2.1
                                have p95_2 := h95c.2.2.1
                                have p95_3 := h95c.2.2.2
                                linarith only [hlam, p95_0]
                          · linarith only [h92, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                          · linarith only [h148, h84, h91, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h148, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h86, h90, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h54, h89, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h54, h84, h88, hlam]
                · linarith only [h0, h83, h87, hlam]
              · linarith only [h0, h82, h86, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h82, h85, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
            · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
              · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                        · linarith only [h0, h163, h54, h82, h84, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h157, h160, h165, h82, h84, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · linarith only [h165, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h158, h162, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h160, h161, h84, hc03, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                        · linarith only [h160, h170, h172, h82, h84, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                            · rcases h3bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h54, hlam, p176_1]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h160, h54, hc23, hc34, hlam, hphi, p176_1]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h84, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h160, h175, h54, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p176_1, u5ehi9]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h160, hc03, hc34, hlam, hphi, p176_1]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h160, h174, h175, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p176_1, u5ehi9]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h160, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h160, h175, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p176_1, u5ehi9]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h82, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h157, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h172, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h160, h175, h54, h82, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p176_1, u5ehi9]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h82, hc34, hlam, hphi, ht23, p176_1, u2ehi2]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h54, hc01, hc34, hlam, hphi, ht12, ht23, p176_1]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [hc34, hlam, hphi, ht23, p176_1, u2ehi2]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                rcases p176_3 (m.d 0 3) (by simp) with h196 | h196
                                · linarith only [h196, h84, hlam]
                                · linarith only [h174, h196, h82, hlam]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h174, h82, hlam, p176_1]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h170, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h174, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [h175, hlam, p176_0]
                              · have p176_0 := h176c.1
                                have p176_1 := h176c.2.1
                                have p176_2 := h176c.2.2.1
                                have p176_3 := h176c.2.2.2
                                linarith only [hlam, p176_0]
                            · linarith only [h174, h175, h82, h84, hlam, hphi, u5ehi8, u5elo4]
                          · linarith only [h174, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h158, h171, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h170, h54, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h159, h83, hlam]
              · linarith only [h0, h158, h83, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h157, h83, hc23, hlam, hphi, u2ehi4]
        · linarith only [h82, h83, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h212 | h212
        · linarith only [h212, h82, hc23, hlam, hphi, u2ehi4]
        · linarith only [h212, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_12_24_L_I_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
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
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h9, hc34, hlam, hphi, u4elo4]
                  · linarith only [h8, hc24, hlam, hphi, u4elo4]
                · linarith only [h7, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h6, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h15, h17, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h17, hc24, hlam, hphi, u4elo4]
                · linarith only [h16, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h15, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h1, h23, h25, h4, hc02, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h25, hc24, hlam, hphi, u4elo4]
                · linarith only [h24, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h23, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · linarith only [h2, h22, h4, hc12, hc25, hlam, hphi]
        · linarith only [h3, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h32 | h32
        · rcases m.htr 0 2 5 (by decide) (by decide) with h33 | h33
          · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
            · linarith only [h0, h2, h32, h34, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
              · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                    · rcases h2bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h36, h37, h39, hc02, hc45, hlam, hphi, ht0b, ht5b, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, h37, h39, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        rcases p40_3 (m.d 0 2) (by simp) with h45 | h45
                        · rcases p40_3 (m.d 1 2) (by simp) with h46 | h46
                          · linarith only [h0, h46, hlam]
                          · linarith only [h2, h36, h37, h39, h46, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1]
                        · linarith only [h45, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h0, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h34, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h0, h37, h39, hc01, hc45, hlam, hphi, ht0b, ht5b, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        rcases p40_3 (m.d 0 2) (by simp) with h54 | h54
                        · rcases p40_3 (m.d 1 2) (by simp) with h55 | h55
                          · rcases p40_3 (m.d 2 3) (by simp) with h56 | h56
                            · rcases p40_3 (m.d 2 4) (by simp) with h57 | h57
                              · linarith only [h36, h57, hlam]
                              · linarith only [h38, h57, hlam]
                            · linarith only [h0, h2, h56, hlam, p40_1]
                          · linarith only [h55, hlam, p40_0]
                        · linarith only [h33, h54, hlam]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h32, h37, h39, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h36, h37, h39, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        rcases p40_3 (m.d 0 2) (by simp) with h66 | h66
                        · linarith only [h2, h66, hlam]
                        · linarith only [h32, h66, hlam]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        rcases p40_3 (m.d 0 2) (by simp) with h69 | h69
                        · linarith only [h2, h69, hlam]
                        · linarith only [h33, h69, hlam]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h32, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h36, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h37, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p40_1, u4elo2]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h33, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h33, h36, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h1, h2, h36, h38, hc02, hlam, hphi, ht23, ht34, p40_1, u4elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h38, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                    · linarith only [h39, hc34, hlam, hphi, u4elo4]
                  · linarith only [h38, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h2, h36, h37, hc24, hlam, hphi, u4elo3]
              · linarith only [h36, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
            · linarith only [h0, h2, h32, h86, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
              · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h33, h88, h90, hlam]
                  · linarith only [h90, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h2, h88, h89, hc24, hlam, hphi, u4elo3]
              · linarith only [h88, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h32, hc02, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h97 | h97
    · rcases m.htr 0 2 3 (by decide) (by decide) with h98 | h98
      · rcases m.htr 0 2 4 (by decide) (by decide) with h99 | h99
        · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
          · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
            · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                    · rcases h2bigk with h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h0, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h103, h105, hc02, hc45, hlam, hphi, ht0b, ht5b, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        rcases p106_3 (m.d 0 2) (by simp) with h110 | h110
                        · rcases p106_3 (m.d 1 2) (by simp) with h111 | h111
                          · rcases p106_3 (m.d 2 3) (by simp) with h112 | h112
                            · linarith only [h112, h98, hlam]
                            · linarith only [h103, h112, hlam]
                          · linarith only [h102, h111, hlam]
                        · linarith only [h110, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        rcases p106_3 (m.d 0 2) (by simp) with h117 | h117
                        · rcases p106_3 (m.d 1 2) (by simp) with h118 | h118
                          · rcases p106_3 (m.d 2 3) (by simp) with h119 | h119
                            · linarith only [h119, h98, hlam]
                            · linarith only [h102, h103, h104, h105, h119, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h0, h102, h104, h118, h97, hlam]
                        · linarith only [h117, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h103, h105, h98, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h103, h105, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        rcases p106_3 (m.d 0 2) (by simp) with h127 | h127
                        · linarith only [h0, h127, hlam]
                        · linarith only [h127, h99, hlam]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        rcases p106_3 (m.d 0 2) (by simp) with h130 | h130
                        · linarith only [h0, h130, hlam]
                        · linarith only [h100, h130, hlam]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h98, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h101, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h103, h105, h98, hc02, hc45, hlam, hphi, ht0b, ht5b, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        rcases p106_3 (m.d 0 2) (by simp) with h137 | h137
                        · rcases p106_3 (m.d 1 2) (by simp) with h138 | h138
                          · rcases p106_3 (m.d 2 3) (by simp) with h139 | h139
                            · rcases p106_3 (m.d 2 4) (by simp) with h140 | h140
                              · linarith only [h103, h140, hlam]
                              · linarith only [h104, h140, hlam]
                            · linarith only [h139, hlam, p106_0]
                          · linarith only [h0, h138, h98, hlam, p106_1]
                        · linarith only [h100, h137, hlam]
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
                        linarith only [h103, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p106_1, u4elo2]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h100, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h102, h103, h104, h105, h97, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p106_1, u4elo0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h104, hlam, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                    · linarith only [h105, hc34, hlam, hphi, u4elo4]
                  · linarith only [h104, hc24, hlam, hphi, u4elo4]
                · linarith only [h103, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h0, h102, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h101, h97, h98, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
            · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
              · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                  · linarith only [h100, h162, h164, h97, hc02, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h164, hc24, hlam, hphi, u4elo4]
                · linarith only [h163, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h162, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · linarith only [h0, h161, h97, h98, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h99, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h171 | h171
        · rcases m.htr 0 2 5 (by decide) (by decide) with h172 | h172
          · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
            · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
              · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h0, h173, h174, h176, h97, h98, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h176, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h174, h175, h97, h98, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h173, h174, h97, h98, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
              · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                  · linarith only [h0, h173, h181, h183, h97, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h183, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h173, h182, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h181, h97, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
            · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
              · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                  · linarith only [h0, h188, h189, h191, h97, h98, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h191, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h190, h98, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h188, h189, h97, h98, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
              · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                · rcases m.htr 2 4 5 (by decide) (by decide) with h198 | h198
                  · linarith only [h0, h188, h196, h198, h97, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h198, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h188, h197, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h196, h97, hc14, hlam, hphi, u4elo2]
        · linarith only [h0, h171, h97, hc14, hlam, hphi, u4elo2]
    · linarith only [h97, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem r1l7_13_24_L_I_H_L (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h10, hc34, hlam, hphi, u4elo4]
                    · linarith only [h9, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h4, h8, hc13, hlam, hphi, ht34, u4elo0]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h16, h18, h19, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h19, hc34, hlam, hphi, u4elo4]
                    · linarith only [h18, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h16, h17, h4, h6, hc24, hlam, hphi, u4elo0]
                · linarith only [h16, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · linarith only [h5, hc04, hlam, hphi, u4elo4]
          · linarith only [h4, hc03, hlam, hphi, ht34, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h29, h3, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                      · rcases h3bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h29, h31, h33, h34, hc03, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h3, hlam, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          rcases p35_3 (m.d 0 3) (by simp) with h39 | h39
                          · rcases p35_3 (m.d 1 3) (by simp) with h40 | h40
                            · linarith only [h1, h40, hlam]
                            · linarith only [h32, h40, hlam]
                          · linarith only [h39, hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          rcases p35_3 (m.d 0 3) (by simp) with h44 | h44
                          · rcases p35_3 (m.d 1 3) (by simp) with h45 | h45
                            · linarith only [h1, h45, hlam]
                            · linarith only [h29, h31, h33, h34, h45, hlam]
                          · linarith only [h44, hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h1, hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h29, hlam, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h1, h34, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          rcases p35_3 (m.d 0 3) (by simp) with h53 | h53
                          · rcases p35_3 (m.d 1 3) (by simp) with h54 | h54
                            · rcases p35_3 (m.d 2 3) (by simp) with h55 | h55
                              · rcases p35_3 (m.d 3 4) (by simp) with h56 | h56
                                · linarith only [h32, h56, hlam]
                                · linarith only [h34, h56, hlam]
                              · linarith only [h1, h3, h55, hlam, p35_1]
                            · linarith only [h54, hlam, p35_0]
                          · linarith only [h0, h3, h31, h33, h34, h53, hlam]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h0, h3, h31, h33, h34, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h29, h31, h33, h34, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          rcases p35_3 (m.d 0 3) (by simp) with h65 | h65
                          · linarith only [h3, h65, hlam]
                          · linarith only [h27, h65, hlam]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          rcases p35_3 (m.d 0 3) (by simp) with h68 | h68
                          · linarith only [h3, h68, hlam]
                          · linarith only [h0, h3, h31, h33, h34, h68, hlam]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h27, hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h32, hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h33, hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h2, h31, h33, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p35_1, u4elo0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h0, h3, h31, h33, h34, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h29, h31, h33, h34, hlam, p35_1]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h2, h31, h33, h34, hc23, hlam, hphi, ht34, p35_1, u4elo0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [h34, hlam, p35_0]
                        · have p35_0 := h35c.1
                          have p35_1 := h35c.2.1
                          have p35_2 := h35c.2.2.1
                          have p35_3 := h35c.2.2.2
                          linarith only [hlam, p35_0]
                      · linarith only [h34, hc34, hlam, hphi, u4elo4]
                    · linarith only [h3, h33, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h29, h31, h32, hc24, hlam, hphi, u4elo3]
                · linarith only [h31, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · linarith only [h28, hc04, hlam, hphi, u4elo4]
          · linarith only [h27, hc03, hlam, hphi, ht34, u4elo3]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
      · rcases m.htr 0 2 3 (by decide) (by decide) with h89 | h89
        · linarith only [h0, h1, h89, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
          · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
            · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
              · linarith only [h0, h1, h89, h93, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                      · linarith only [h0, h1, h93, h95, h97, h98, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h98, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h1, h93, h97, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h1, h91, h95, h96, hc24, hlam, hphi, u4elo0]
                · linarith only [h95, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · linarith only [h92, hc04, hlam, hphi, u4elo4]
          · linarith only [h1, h91, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
      · linarith only [h0, h88, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h107 | h107
    · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
      · rcases m.htr 0 2 3 (by decide) (by decide) with h109 | h109
        · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
          · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
            · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
              · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                      · linarith only [h0, h107, h112, h115, h116, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h116, hc34, hlam, hphi, u4elo4]
                    · linarith only [h115, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h110, h114, hc13, hlam, hphi, ht34, u4elo0]
                · linarith only [h0, h113, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h107, h109, h112, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h111, hc04, hlam, hphi, u4elo4]
          · linarith only [h110, hc03, hlam, hphi, ht34, u4elo3]
        · linarith only [h0, h107, h109, hlam]
      · linarith only [h108, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h127 | h127
      · rcases m.htr 0 2 3 (by decide) (by decide) with h128 | h128
        · rcases m.htr 0 3 4 (by decide) (by decide) with h129 | h129
          · rcases m.htr 0 4 5 (by decide) (by decide) with h130 | h130
            · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
              · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                      · rcases h3bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h107, hlam, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h134, h135, hc03, hc45, hlam, hphi, ht0b, ht5b, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          rcases p136_3 (m.d 0 3) (by simp) with h140 | h140
                          · rcases p136_3 (m.d 1 3) (by simp) with h141 | h141
                            · rcases p136_3 (m.d 2 3) (by simp) with h142 | h142
                              · linarith only [h128, h142, hlam]
                              · linarith only [h134, h142, hlam]
                            · linarith only [h133, h141, hlam]
                          · linarith only [h140, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          rcases p136_3 (m.d 0 3) (by simp) with h147 | h147
                          · rcases p136_3 (m.d 1 3) (by simp) with h148 | h148
                            · rcases p136_3 (m.d 2 3) (by simp) with h149 | h149
                              · linarith only [h128, h149, hlam]
                              · linarith only [h134, h135, h149, hlam]
                            · linarith only [h107, h127, h132, h134, h135, h148, hlam]
                          · linarith only [h147, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h107, h127, h132, h134, h135, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h131, h134, h135, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          rcases p136_3 (m.d 0 3) (by simp) with h157 | h157
                          · linarith only [h107, h157, hlam]
                          · linarith only [h129, h157, hlam]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          rcases p136_3 (m.d 0 3) (by simp) with h160 | h160
                          · linarith only [h107, h160, hlam]
                          · linarith only [h107, h127, h132, h134, h135, h160, hlam]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h128, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h131, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h128, h135, hc02, hc45, hlam, hphi, ht0b, ht5b, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          rcases p136_3 (m.d 0 3) (by simp) with h167 | h167
                          · rcases p136_3 (m.d 1 3) (by simp) with h168 | h168
                            · rcases p136_3 (m.d 2 3) (by simp) with h169 | h169
                              · rcases p136_3 (m.d 3 4) (by simp) with h170 | h170
                                · linarith only [h134, h170, hlam]
                                · linarith only [h135, h170, hlam]
                              · linarith only [h169, hlam, p136_0]
                            · linarith only [h0, h107, h127, h128, h132, h134, h135, h168, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p136_1]
                          · linarith only [h128, h167, hlam, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h129, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h133, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h134, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h107, h127, h132, h134, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h107, h127, h132, h134, h135, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h132, h134, h135, hc13, hlam, hphi, ht34, p136_1, u4elo1]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h127, h132, h134, h135, hc23, hlam, hphi, ht34, p136_1, u4elo0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [h135, hlam, p136_0]
                        · have p136_0 := h136c.1
                          have p136_1 := h136c.2.1
                          have p136_2 := h136c.2.2.1
                          have p136_3 := h136c.2.2.2
                          linarith only [hlam, p136_0]
                      · linarith only [h135, hc34, hlam, hphi, u4elo4]
                    · linarith only [h134, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h107, h129, h133, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                · linarith only [h0, h132, hc02, hlam, hphi, ht23, ht34, u4elo2]
              · linarith only [h0, h127, h128, h131, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h130, hc04, hlam, hphi, u4elo4]
          · linarith only [h107, h127, h129, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
          · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
            · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
              · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h199 | h199
                      · linarith only [h0, h127, h128, h195, h196, h198, h199, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h199, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h128, h198, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h127, h128, h193, h195, h196, h197, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h128, h195, h196, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                      · linarith only [h0, h127, h195, h205, h207, h208, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h208, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h195, h207, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h127, h193, h195, h205, h206, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h205, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h194, hc04, hlam, hphi, u4elo4]
          · linarith only [h193, hc03, hlam, hphi, ht34, u4elo3]
      · linarith only [h127, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

end R2N4
